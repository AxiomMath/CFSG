module

public import CFSG.RankThree.PartTwo.Sec11.Item1115NotFieldProofMho

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Item1115NotFieldProof

section Wreath

theorem false_of_wreath_quotient_cube {P : Type*} [Group P] {Q : Subgroup P} [Q.Normal]
    (e : P ⧸ Q ≃* W33) {r g s x : P}
    (hrg : r * g * r⁻¹ * g⁻¹ ∈ Subgroup.closure {s ^ 3, x ^ 3}) (hsx : s * x = x * s)
    (hPP : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.closure {s, x})
    (htop : Subgroup.closure {r, g} ⊔ Subgroup.closure {s, x} = ⊤) : False := by
  set π : P →* W33 := e.toMonoidHom.comp (QuotientGroup.mk' Q) with hπdef
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top.mpr hπ
  have hpair : ∀ a b : P, (Subgroup.closure ({a, b} : Set P)).map π =
      Subgroup.closure {π a, π b} := by
    intro a b
    rw [MonoidHom.map_closure, Set.image_pair]
  have hcomm : ⁅(⊤ : Subgroup W33), ⊤⁆ ≤ Subgroup.closure {π s, π x} := by
    have h1 : (⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ : Subgroup P).map π =
        ⁅(⊤ : Subgroup W33), ⊤⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange]
    rw [← h1, ← hpair]
    exact Subgroup.map_mono hPP
  have hsx' : π s * π x = π x * π s := by rw [← map_mul, ← map_mul, hsx]
  have hkD : wreathK ∈ Subgroup.closure ({π s, π x} : Set W33) :=
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hs3 : π s ^ 3 = 1 := pow_three_eq_one_of_right_eq_one (right_eq_one_of_commute_wreathK
    (mul_comm_of_mem_closure_pair hsx' (Subgroup.subset_closure (by simp)) hkD))
  have hx3 : π x ^ 3 = 1 := pow_three_eq_one_of_right_eq_one (right_eq_one_of_commute_wreathK
    (mul_comm_of_mem_closure_pair hsx' (Subgroup.subset_closure (by simp)) hkD))
  have hrg' : π r * π g = π g * π r := by
    have h1 : π (r * g * r⁻¹ * g⁻¹) ∈ Subgroup.closure ({π (s ^ 3), π (x ^ 3)} : Set W33) := by
      rw [← hpair]
      exact Subgroup.mem_map_of_mem π hrg
    rw [map_pow, map_pow, hs3, hx3, Set.pair_eq_singleton, Subgroup.closure_singleton_one,
      Subgroup.mem_bot, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π r * π g = (π r * π g * (π r)⁻¹ * (π g)⁻¹) * (π g * π r) := by group
      _ = π g * π r := by rw [h1, one_mul]
  refine false_of_abelian_supplement (S := (Subgroup.closure {r, g}).map π) (d₁ := π s)
    (d₂ := π x) ?_ hsx' hcomm ?_
  · intro a ha b hb
    rw [hpair] at ha hb
    exact mul_comm_of_mem_closure_pair hrg' ha hb
  · rw [← hpair, ← Subgroup.map_sup, htop, ← MonoidHom.range_eq_map, hrange]

theorem false_of_wreath_quotient_cube_of_le {G : Type*} [Group G] {P : Subgroup G}
    {K : Subgroup P} [K.Normal] (e : P ⧸ K ≃* W33) {r g s x : G} (hr : r ∈ P) (hg : g ∈ P)
    (hs : s ∈ P) (hx : x ∈ P) (hrg : r * g * r⁻¹ * g⁻¹ ∈ Subgroup.closure {s ^ 3, x ^ 3})
    (hsx : s * x = x * s) (hPP : ⁅P, P⁆ ≤ Subgroup.closure {s, x})
    (htop : P ≤ Subgroup.closure {r, g} ⊔ Subgroup.closure {s, x}) : False := by
  have hpair : ∀ (a b : G) (ha : a ∈ P) (hb : b ∈ P),
      (Subgroup.closure ({⟨a, ha⟩, ⟨b, hb⟩} : Set P)).map P.subtype = Subgroup.closure {a, b} := by
    intro a b ha hb
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have htopP : (⊤ : Subgroup P).map P.subtype = P := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine false_of_wreath_quotient_cube e (r := ⟨r, hr⟩) (g := ⟨g, hg⟩) (s := ⟨s, hs⟩)
    (x := ⟨x, hx⟩) ?_ (Subtype.ext hsx) ?_ ?_
  · have hs3 : (⟨s, hs⟩ : P) ^ 3 = ⟨s ^ 3, P.pow_mem hs 3⟩ := Subtype.ext (by simp)
    have hx3 : (⟨x, hx⟩ : P) ^ 3 = ⟨x ^ 3, P.pow_mem hx 3⟩ := Subtype.ext (by simp)
    rw [hs3, hx3, ← Subgroup.mem_map_iff_mem P.subtype_injective, hpair]
    exact hrg
  · rw [← Subgroup.map_le_map_iff_of_injective P.subtype_injective, Subgroup.map_commutator,
      htopP, hpair]
    exact hPP
  · apply eq_top_iff.mpr
    rw [← Subgroup.map_le_map_iff_of_injective P.subtype_injective, htopP, Subgroup.map_sup,
      hpair, hpair]
    exact htop

end Wreath

section Data

variable {G : Type} [Group G] [Finite G]
variable {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}

theorem mhoHyp_a (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hsa : s * a ≠ a * s) : Item1115Proof.MhoHyp a s x a := by
  have haR : a ∈ R := Item1115Proof.A_le_R h.toHyp91 h.a_mem
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  exact
    { commute_s_x := h.commute_s_x
      inf_eq_bot := Item1115Proof.inf_zpowers_eq_bot h
      r_mem_normalizer_s := Item1115Proof.mem_normalizer_zpowers_s h45 h haR
      r_mem_normalizer_x := Item1115Proof.mem_normalizer_zpowers_x h45 h haR
      pow_r := ⟨1, by rw [pow_one]; exact h.mem_partTwoF.1.2 a h.a_mem⟩
      pow_s := Item1116Proof.exists_pow_eq_one_of_mem h hsR
      pow_x := Item1116Proof.exists_pow_eq_one_of_mem h hxR
      a_mem := Subgroup.mem_zpowers a
      a_ne_one := h.a_ne_one
      a_cube := h.mem_partTwoF.1.2 a h.a_mem
      not_commute_s := fun e => hsa e.symm
      not_commute_x := Item1115Proof.not_commute_a_x h }

theorem mem_closure_cube_of_commute (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hsa : s * a ≠ a * s) {v : G} (hv : v ∈ Subgroup.closure ({s, x} : Set G))
    (hav : a * v = v * a) : v ∈ Subgroup.closure ({s ^ 3, x ^ 3} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := (mhoHyp_a h45 h hsa).mem_closure_pow_of_commute (Subgroup.mem_zpowers a) hv hav
  rwa [orderOf_eq_prime (h.mem_partTwoF.1.2 a h.a_mem) h.a_ne_one] at h1

theorem commutator_le_V_of_mem (h : Sec11Data G A c L a R Y d x s r g)
    (hrg : r * g * r⁻¹ * g⁻¹ ∈ Subgroup.closure ({s, x} : Set G))
    (hRV : R ≤ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G))
    (hgV : g ∈ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G)) :
    ⁅sec11P R g, sec11P R g⁆ ≤ Subgroup.closure {s, x} := by
  set V := Subgroup.closure ({s, x} : Set G) with hVdef
  obtain ⟨hrR, -, -⟩ := Item1116Proof.mem_R h
  have hsV : s ∈ V := Subgroup.subset_closure (by simp)
  have hxV : x ∈ V := Subgroup.subset_closure (by simp)
  have hPT : sec11P R g ≤ Subgroup.closure {r, g, s, x} := by
    refine sup_le ?_ ?_
    · rw [h.R_eq, Subgroup.closure_le]
      rintro y (rfl | rfl | rfl) <;> exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
  have hTN : ∀ y ∈ ({r, g, s, x} : Set G), y ∈ Subgroup.normalizer (V : Set G) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy | hy <;> rw [hy]
    exacts [hRV hrR, hgV, Subgroup.le_normalizer hsV, Subgroup.le_normalizer hxV]
  have hrg' : ⁅r, g⁆ ∈ V := by
    rw [commutatorElement_def]
    exact hrg
  have hgr' : ⁅g, r⁆ ∈ V := by
    rw [← commutatorElement_inv]
    exact V.inv_mem hrg'
  refine (Subgroup.commutator_mono hPT hPT).trans (commutator_closure_le ?_ ?_)
  · rw [Subgroup.closure_le]
    exact hTN
  · intro y hy z hz
    have hyN := hTN y hy
    have hzN := hTN z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy hz
    rcases hy with hy | hy | hy | hy
    · rcases hz with hz | hz | hz | hz
      · rw [hy, hz, commutatorElement_self]
        exact V.one_mem
      · rw [hy, hz]
        exact hrg'
      · exact commutator_mem_of_mem_right hyN (by rw [hz]; exact hsV)
      · exact commutator_mem_of_mem_right hyN (by rw [hz]; exact hxV)
    · rcases hz with hz | hz | hz | hz
      · rw [hy, hz]
        exact hgr'
      · rw [hy, hz, commutatorElement_self]
        exact V.one_mem
      · exact commutator_mem_of_mem_right hyN (by rw [hz]; exact hsV)
      · exact commutator_mem_of_mem_right hyN (by rw [hz]; exact hxV)
    · exact commutator_mem_of_mem_left (by rw [hy]; exact hsV) hzN
    · exact commutator_mem_of_mem_left (by rw [hy]; exact hxV) hzN

theorem false_of_core (h : Sec11Data G A c L a R Y d x s r g)
    (hrg : r * g * r⁻¹ * g⁻¹ ∈ Subgroup.closure ({s ^ 3, x ^ 3} : Set G))
    (hPP : ⁅sec11P R g, sec11P R g⁆ ≤ Subgroup.closure {s, x})
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
  rcases rank3II_11_14_mem h hcdN hNd htrans hVP hPP hNV hrP hcen with ⟨K, hK, ⟨e⟩⟩ | hr
  · refine false_of_wreath_quotient_cube_of_le e hrP hgP hsP hxP hrg h.commute_s_x hPP ?_
    refine sup_le ?_ ?_
    · rw [h.R_eq, Subgroup.closure_le]
      rintro y (rfl | rfl | rfl)
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_right hxV
      · exact Subgroup.mem_sup_right hsV
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  · exact hrV hr

theorem false_of_commutator_mem_V (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hra : r * a = a * r)
    (hrg : r * g * r⁻¹ * g⁻¹ ∈ Subgroup.closure ({s, x} : Set G)) (hsa : s * a ≠ a * s) :
    False := by
  have hRV := h.R_le_normalizer_V h45
  have hgV := normalizer_R_le_V h45 h hsa h.g_mem_normalizer
  have hPP := commutator_le_V_of_mem h hrg hRV hgV
  have hcdN := Item1115Proof.normalizer_P_le_cd h113 h hPP hsa
  have htrans := h.htrans_of_mem_normalizer (Item1115Proof.W_le_normalizer_d h117 h h.g_mem.2)
  have hNd := Item1115Proof.normalizer_P_le_d h113 h117 h hcdN htrans
  have hgC : g ∈ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y h.g_mem.1
  have hrC : r ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hra
  have hrgC : r * g * r⁻¹ * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G) :=
    mul_mem (mul_mem (mul_mem hrC hgC) (inv_mem hrC)) (inv_mem hgC)
  have hrg3 := mem_closure_cube_of_commute h45 h hsa hrg
    (Subgroup.mem_centralizer_singleton_iff.mp hrgC).symm
  exact false_of_core h hrg3 hPP (h.normalizer_P_le_normalizer_V h45 h113)
    (h.commutator_mem_V h45 h113 outAbelian1016 (Item1116Proof.mem_R h).1) h.r_not_mem_V hcdN hNd
    htrans

theorem commute_s_a_of_commute (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hra : r * a = a * r) : s * a = a * s := by
  by_contra hsa
  exact false_of_commutator_mem_V h45 h113 h117 h hra (commutator_r_g_mem_V h45 h hsa) hsa

end Data

end Item1115NotFieldProof

section Main

theorem item1115_of_mhoV (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117) : Item1115 := by
  intro G _ _ A c L a R Y d x s r g h
  by_contra hsa
  obtain ⟨r₁, h₁, hr₁a⟩ := rank3II_11_11_choose h (h.closure_rs_le_normalizer h45 h113) hsa
  exact hsa (Item1115NotFieldProof.commute_s_a_of_commute h45 h113 h117 h₁ hr₁a)

end Main

end CFSG.RankThree.PartTwo.Sec11
