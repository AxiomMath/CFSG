module

public import CFSG.RankThree.PartTwo.Sec11.Final
public import CFSG.RankThree.PartTwo.Sec11.Coprime
public import CFSG.RankThree.PartTwo.Sec11.WreathSupplement

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_closure_le {T : Set G} {V : Subgroup G}
    (hN : Subgroup.closure T ≤ Subgroup.normalizer (V : Set G))
    (hT : ∀ a ∈ T, ∀ b ∈ T, ⁅a, b⁆ ∈ V) :
    ⁅Subgroup.closure T, Subgroup.closure T⁆ ≤ V := by
  have hconj : ∀ y ∈ Subgroup.closure T, ∀ v ∈ V, y * v * y⁻¹ ∈ V := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hN hy) v).mp hv
  have h1 : ∀ a ∈ T, ∀ y ∈ Subgroup.closure T, ⁅a, y⁆ ∈ V := by
    intro a ha y hy
    induction hy using Subgroup.closure_induction with
    | mem b hb => exact hT a ha b hb
    | one => simp
    | mul y z hy hz ihy ihz =>
      have e : ⁅a, y * z⁆ = ⁅a, y⁆ * (y * ⁅a, z⁆ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact V.mul_mem ihy (hconj y hy _ ihz)
    | inv y hy ihy =>
      have e : ⁅a, y⁻¹⁆ = y⁻¹ * ⁅a, y⁆⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hconj y⁻¹ (inv_mem hy) _ (V.inv_mem ihy)
  have h2 : ∀ y ∈ Subgroup.closure T, ∀ x ∈ Subgroup.closure T, ⁅x, y⁆ ∈ V := by
    intro y hy x hx
    induction hx using Subgroup.closure_induction with
    | mem a ha => exact h1 a ha y hy
    | one => simp
    | mul x w hx hw ihx ihw =>
      have e : ⁅x * w, y⁆ = x * ⁅w, y⁆ * x⁻¹ * ⁅x, y⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact V.mul_mem (hconj x hx _ ihw) ihx
    | inv x hx ihx =>
      have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hconj x⁻¹ (inv_mem hx) _ (V.inv_mem ihx)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact h2 y hy x hx

theorem commutator_mem_of_mem_left {V : Subgroup G} {a b : G} (ha : a ∈ V)
    (hb : b ∈ Subgroup.normalizer (V : Set G)) : ⁅a, b⁆ ∈ V := by
  rw [commutatorElement_def, mul_assoc, mul_assoc]
  refine V.mul_mem ha ?_
  rw [← mul_assoc]
  exact (Subgroup.mem_normalizer_iff.mp hb a⁻¹).mp (V.inv_mem ha)

theorem commutator_mem_of_mem_right {V : Subgroup G} {a b : G}
    (ha : a ∈ Subgroup.normalizer (V : Set G)) (hb : b ∈ V) : ⁅a, b⁆ ∈ V := by
  rw [commutatorElement_def]
  exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp ha b).mp hb) (V.inv_mem hb)

theorem le_normalizer_commutator (P X : Subgroup G) :
    P ≤ Subgroup.normalizer ((⁅P, X⁆ : Subgroup G) : Set G) := by
  have hgen : ∀ p ∈ P, ∀ q ∈ P, ∀ k ∈ X, p * ⁅q, k⁆ * p⁻¹ ∈ ⁅P, X⁆ := by
    intro p hp q hq k hk
    have e : p * ⁅q, k⁆ * p⁻¹ = ⁅p * q, k⁆ * ⁅p, k⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (P.mul_mem hp hq) hk)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hp hk))
  have hconj : ∀ p ∈ P, ∀ z ∈ ⁅P, X⁆, p * z * p⁻¹ ∈ ⁅P, X⁆ := by
    intro p hp z hz
    rw [Subgroup.commutator_def] at hz
    induction hz using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨q, hq, k, hk, rfl⟩ := hw
      exact hgen p hp q hq k hk
    | one => simp
    | mul y z _ _ ihy ihz =>
      have e : p * (y * z) * p⁻¹ = (p * y * p⁻¹) * (p * z * p⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ihy ihz
    | inv y _ ihy =>
      have e : p * y⁻¹ * p⁻¹ = (p * y * p⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ihy
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact hconj p hp z
  · intro hz
    have := hconj p⁻¹ (P.inv_mem hp) _ hz
    simpa [mul_assoc] using this

theorem false_of_wreath_quotient_of_le {P : Subgroup G} {K : Subgroup P} [K.Normal]
    (e : P ⧸ K ≃* W33) {r g s x : G} (hr : r ∈ P) (hg : g ∈ P) (hs : s ∈ P) (hx : x ∈ P)
    (hrg : r * g = g * r) (hsx : s * x = x * s)
    (hPP : ⁅P, P⁆ ≤ Subgroup.closure {s, x})
    (htop : P ≤ Subgroup.closure {r, g} ⊔ Subgroup.closure {s, x}) : False := by
  have hpair : ∀ (a b : G) (ha : a ∈ P) (hb : b ∈ P),
      (Subgroup.closure ({⟨a, ha⟩, ⟨b, hb⟩} : Set P)).map P.subtype = Subgroup.closure {a, b} := by
    intro a b ha hb
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have htopP : (⊤ : Subgroup P).map P.subtype = P := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine false_of_wreath_quotient e (r := ⟨r, hr⟩) (g := ⟨g, hg⟩) (s := ⟨s, hs⟩) (x := ⟨x, hx⟩)
    (Subtype.ext hrg) (Subtype.ext hsx) ?_ ?_
  · rw [← Subgroup.map_le_map_iff_of_injective P.subtype_injective, Subgroup.map_commutator,
      htopP, hpair]
    exact hPP
  · apply eq_top_iff.mpr
    rw [← Subgroup.map_le_map_iff_of_injective P.subtype_injective, htopP, Subgroup.map_sup,
      hpair, hpair]
    exact htop

theorem rank3II_11_14_mem {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g)
    (hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hNd : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (htrans : ∀ F : Subgroup G, F ≤ Subgroup.closure {c, d} →
      Nat.card F = Nat.card (Subgroup.zpowers c) → F ≠ Subgroup.zpowers d →
        ∃ p ∈ sec11P R g, F = (Subgroup.zpowers c).map (MulAut.conj p).toMonoidHom)
    {V : Subgroup G} (hVP : V ≤ sec11P R g) (hPP : ⁅sec11P R g, sec11P R g⁆ ≤ V)
    (hNV : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (V : Set G))
    {y : G} (hy : y ∈ sec11P R g)
    (hcen : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G), n * y * n⁻¹ * y⁻¹ ∈ V) :
    (∃ (K : Subgroup (sec11P R g)) (_ : K.Normal), Nonempty (sec11P R g ⧸ K ≃* W33)) ∨
      y ∈ V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases rank3II_11_14 h hcdN hNd htrans with hW | hP
  · exact Or.inl hW
  · right
    have hRP : R ≤ sec11P R g := le_sup_left
    have hRN : R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
        Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) :=
      le_inf h.isSylowOf.le (hRP.trans Subgroup.le_normalizer)
    have hS := h.isSylowOf.of_le hRN inf_le_left
    have htop : sec11P R g ≤ V ⊔ ⁅Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
        Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G), sec11P R g⁆ := by
      conv_lhs => rw [hP]
      exact sup_le_sup_right hPP _
    exact mem_of_commutator_mem_of_coprime h.isPGroup_sec11P hVP hPP inf_le_right hNV hS hRP
      htop hy hcen

theorem rank3II_11_22_mem {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g)
    (hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hNd : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (htrans : ∀ F : Subgroup G, F ≤ Subgroup.closure {c, d} →
      Nat.card F = Nat.card (Subgroup.zpowers c) → F ≠ Subgroup.zpowers d →
        ∃ p ∈ sec11P R g, F = (Subgroup.zpowers c).map (MulAut.conj p).toMonoidHom)
    (hW : ∀ (K : Subgroup (sec11P R g)) [K.Normal], IsEmpty (sec11P R g ⧸ K ≃* W33))
    {V : Subgroup G} (hVP : V ≤ sec11P R g) (hPP : ⁅sec11P R g, sec11P R g⁆ ≤ V)
    (hNV : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (V : Set G))
    {y : G} (hy : y ∈ sec11P R g)
    (hcen : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G), n * y * n⁻¹ * y⁻¹ ∈ V) :
    y ∈ V := by
  rcases rank3II_11_14_mem h hcdN hNd htrans hVP hPP hNV hy hcen with ⟨K, hK, ⟨e⟩⟩ | hyV
  · exact ((hW K).false e).elim
  · exact hyV

theorem rank3II_11_15_of {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) (hrg : r * g = g * r) (hsx : s * x = x * s)
    (hRV : R ≤ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G))
    (hgV : g ∈ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G))
    (hNV : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G))
    (hcen : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
        n * r * n⁻¹ * r⁻¹ ∈ Subgroup.closure {s, x})
    (hrV : r ∉ Subgroup.closure {s, x})
    (hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hNd : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (htrans : ∀ F : Subgroup G, F ≤ Subgroup.closure {c, d} →
      Nat.card F = Nat.card (Subgroup.zpowers c) → F ≠ Subgroup.zpowers d →
        ∃ p ∈ sec11P R g, F = (Subgroup.zpowers c).map (MulAut.conj p).toMonoidHom) :
    False := by
  set V := Subgroup.closure ({s, x} : Set G) with hVdef
  have hmemR : ∀ y ∈ ({r, x, s} : Set G), y ∈ R := by
    intro y hy
    rw [h.R_eq]
    exact Subgroup.subset_closure hy
  have hRP : R ≤ sec11P R g := le_sup_left
  have hrP : r ∈ sec11P R g := hRP (hmemR r (by simp))
  have hxP : x ∈ sec11P R g := hRP (hmemR x (by simp))
  have hsP : s ∈ sec11P R g := hRP (hmemR s (by simp))
  have hgP : g ∈ sec11P R g :=
    (le_sup_right : Subgroup.zpowers g ≤ sec11P R g) (Subgroup.mem_zpowers g)
  have hsV : s ∈ V := Subgroup.subset_closure (by simp)
  have hxV : x ∈ V := Subgroup.subset_closure (by simp)
  have hVP : V ≤ sec11P R g := by
    rw [hVdef, Subgroup.closure_le]
    rintro y (rfl | rfl)
    exacts [hsP, hxP]
  have hPT : sec11P R g ≤ Subgroup.closure {r, g, s, x} := by
    refine sup_le ?_ ?_
    · rw [h.R_eq, Subgroup.closure_le]
      rintro y (rfl | rfl | rfl) <;> exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
  have hNVr : r ∈ Subgroup.normalizer (V : Set G) := hRV (hmemR r (by simp))
  have hVN : ∀ v ∈ V, v ∈ Subgroup.normalizer (V : Set G) := fun v hv => Subgroup.le_normalizer hv
  have hTN : ∀ y ∈ ({r, g, s, x} : Set G), y ∈ Subgroup.normalizer (V : Set G) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy | hy <;> rw [hy]
    exacts [hNVr, hgV, hVN s hsV, hVN x hxV]
  have hPP : ⁅sec11P R g, sec11P R g⁆ ≤ V := by
    refine (Subgroup.commutator_mono hPT hPT).trans (commutator_closure_le ?_ ?_)
    · rw [Subgroup.closure_le]
      exact hTN
    · have hrg' : ⁅r, g⁆ = 1 := by rw [commutatorElement_eq_one_iff_mul_comm, hrg]
      have hgr' : ⁅g, r⁆ = 1 := by rw [commutatorElement_eq_one_iff_mul_comm, hrg]
      intro y hy z hz
      have hyN := hTN y hy
      have hzN := hTN z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy hz
      rcases hy with hy | hy | hy | hy
      · rcases hz with hz | hz | hz | hz
        · rw [hy, hz, commutatorElement_self]
          exact V.one_mem
        · rw [hy, hz, hrg']
          exact V.one_mem
        · exact commutator_mem_of_mem_right hyN (by rw [hz]; exact hsV)
        · exact commutator_mem_of_mem_right hyN (by rw [hz]; exact hxV)
      · rcases hz with hz | hz | hz | hz
        · rw [hy, hz, hgr']
          exact V.one_mem
        · rw [hy, hz, commutatorElement_self]
          exact V.one_mem
        · exact commutator_mem_of_mem_right hyN (by rw [hz]; exact hsV)
        · exact commutator_mem_of_mem_right hyN (by rw [hz]; exact hxV)
      · exact commutator_mem_of_mem_left (by rw [hy]; exact hsV) hzN
      · exact commutator_mem_of_mem_left (by rw [hy]; exact hxV) hzN
  rcases rank3II_11_14_mem h hcdN hNd htrans hVP hPP hNV hrP hcen with ⟨K, hK, ⟨e⟩⟩ | hr
  · refine false_of_wreath_quotient_of_le e hrP hgP hsP hxP hrg hsx hPP ?_
    refine sup_le ?_ ?_
    · rw [h.R_eq, Subgroup.closure_le]
      rintro y (rfl | rfl | rfl)
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_right hxV
      · exact Subgroup.mem_sup_right hsV
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  · exact hrV hr

theorem rank3II_11_27_of {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g)
    (hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hNd : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (htrans : ∀ F : Subgroup G, F ≤ Subgroup.closure {c, d} →
      Nat.card F = Nat.card (Subgroup.zpowers c) → F ≠ Subgroup.zpowers d →
        ∃ p ∈ sec11P R g, F = (Subgroup.zpowers c).map (MulAut.conj p).toMonoidHom)
    (hW : ∀ (K : Subgroup (sec11P R g)) [K.Normal], IsEmpty (sec11P R g ⧸ K ≃* W33))
    (hVP : Subgroup.closure ({x, s} : Set G) ≤ sec11P R g)
    (hNV : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((Subgroup.closure {x, s} : Subgroup G) : Set G))
    (haP : a ∈ sec11P R g)
    (hcen : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
        n * a * n⁻¹ * a⁻¹ ∈ Subgroup.closure {x, s})
    (haV : a ∉ Subgroup.closure {x, s}) :
    ¬ ⁅sec11P R g, sec11P R g⁆ ≤ Subgroup.closure {x, s} := fun hPP =>
  haV (rank3II_11_22_mem h hcdN hNd htrans hW hVP hPP hNV haP hcen)

end CFSG.RankThree.PartTwo.Sec11
