module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.A1cRankLemmas

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace F6

section Commutator

variable {G : Type*} [Group G]

theorem commutatorElement_mul_right' (g h₁ h₂ : G) :
    ⁅g, h₁ * h₂⁆ = ⁅g, h₁⁆ * (h₁ * ⁅g, h₂⁆ * h₁⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_left' (g₁ g₂ h : G) :
    ⁅g₁ * g₂, h⁆ = g₁ * ⁅g₂, h⁆ * g₁⁻¹ * ⁅g₁, h⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_inv_right' (g h : G) : ⁅g, h⁻¹⁆ = h⁻¹ * ⁅g, h⁆⁻¹ * h := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_inv_left' (g h : G) : ⁅g⁻¹, h⁆ = g⁻¹ * ⁅g, h⁆⁻¹ * g := by
  simp only [commutatorElement_def]
  group

theorem commutator_closure_pair_le (x y : G) (M : Subgroup G) [M.Normal]
    (h : ⁅⁅Subgroup.closure ({x, y} : Set G), Subgroup.closure ({x, y} : Set G)⁆,
      Subgroup.closure ({x, y} : Set G)⁆ ≤ M) :
    ⁅Subgroup.closure ({x, y} : Set G), Subgroup.closure ({x, y} : Set G)⁆ ≤
      Subgroup.zpowers ⁅x, y⁆ ⊔ M := by
  set L := Subgroup.closure ({x, y} : Set G) with hLdef
  set π := QuotientGroup.mk' M with hπ
  set L' := L.map π with hL'def
  have hL' : L' = Subgroup.closure ({π x, π y} : Set (G ⧸ M)) := by
    rw [hL'def, hLdef, MonoidHom.map_closure, Set.image_pair]
  have hcl : ⁅⁅L', L'⁆, L'⁆ = ⊥ := by
    rw [hL'def, ← Subgroup.map_commutator, ← Subgroup.map_commutator, eq_bot_iff,
      Subgroup.map_le_iff_le_comap]
    refine h.trans fun m hm => ?_
    rw [Subgroup.mem_comap, Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff m).mpr hm
  have hcent : ∀ z ∈ ⁅L', L'⁆, ∀ g ∈ L', g * z * g⁻¹ = z := by
    intro z hz g hg
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcl hz
    rw [Subgroup.mem_centralizer_iff.mp h1 g hg, mul_inv_cancel_right]
  set c := ⁅π x, π y⁆ with hc
  have hright : ∀ g ∈ L', (∀ h ∈ ({π x, π y} : Set (G ⧸ M)), ⁅g, h⁆ ∈ Subgroup.zpowers c) →
      ∀ h ∈ L', ⁅g, h⁆ ∈ Subgroup.zpowers c := by
    intro g hg hgen h hh
    rw [hL'] at hh
    induction hh using Subgroup.closure_induction with
    | mem h hmem => exact hgen h hmem
    | one => rw [commutatorElement_one_right]; exact Subgroup.one_mem _
    | mul h₁ h₂ hh₁ hh₂ ih₁ ih₂ =>
      rw [commutatorElement_mul_right', hcent _ (Subgroup.commutator_mem_commutator hg
        (hL' ▸ hh₂)) _ (hL' ▸ hh₁)]
      exact Subgroup.mul_mem _ ih₁ ih₂
    | inv h hh ih =>
      have h1 := hcent _ (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hg (hL' ▸ hh)))
        _ (Subgroup.inv_mem _ (hL' ▸ hh))
      rw [inv_inv] at h1
      rw [commutatorElement_inv_right', h1]
      exact Subgroup.inv_mem _ ih
  have hx : π x ∈ L' := hL' ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hy : π y ∈ L' := hL' ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hgen : ∀ g ∈ ({π x, π y} : Set (G ⧸ M)), ∀ h ∈ L', ⁅g, h⁆ ∈ Subgroup.zpowers c := by
    rintro g (rfl | rfl)
    · refine hright _ hx ?_
      rintro h (rfl | rfl)
      · rw [commutatorElement_self]; exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    · refine hright _ hy ?_
      rintro h (rfl | rfl)
      · rw [← commutatorElement_inv, ← hc]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
      · rw [commutatorElement_self]; exact Subgroup.one_mem _
  have hleft : ∀ g ∈ L', ∀ h ∈ L', ⁅g, h⁆ ∈ Subgroup.zpowers c := by
    intro g hg
    rw [hL'] at hg
    induction hg using Subgroup.closure_induction with
    | mem g hmem => exact hgen g hmem
    | one => intro h _; rw [commutatorElement_one_left]; exact Subgroup.one_mem _
    | mul g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
      intro h hh
      rw [commutatorElement_mul_left', hcent _ (Subgroup.commutator_mem_commutator
        (hL' ▸ hg₂) hh) _ (hL' ▸ hg₁)]
      exact Subgroup.mul_mem _ (ih₂ h hh) (ih₁ h hh)
    | inv g hg ih =>
      intro h hh
      have h1 := hcent _ (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator (hL' ▸ hg) hh))
        _ (Subgroup.inv_mem _ (hL' ▸ hg))
      rw [inv_inv] at h1
      rw [commutatorElement_inv_left', h1]
      exact Subgroup.inv_mem _ (ih h hh)
  have hle : ⁅L', L'⁆ ≤ Subgroup.zpowers c := Subgroup.commutator_le.mpr hleft
  rw [hL'def, ← Subgroup.map_commutator, hc, ← map_commutatorElement, ← MonoidHom.map_zpowers,
    Subgroup.map_le_iff_le_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hle
  exact hle

end Commutator

section ClassThree

variable {G : Type*} [Group G]

theorem commute_of_mem_closure_pair {u w z₁ z₂ : G} (huw : Commute u w)
    (h₁ : z₁ ∈ Subgroup.closure ({u, w} : Set G)) (h₂ : z₂ ∈ Subgroup.closure ({u, w} : Set G)) :
    Commute z₁ z₂ := by
  have hk : ({u, w} : Set G).Pairwise Commute := by
    rintro a (rfl | rfl) b (rfl | rfl) _
    · exact Commute.refl _
    · exact huw
    · exact huw.symm
    · exact Commute.refl _
  have hc := Subgroup.closure_le_centralizer_centralizer ({u, w} : Set G)
  exact Set.centralizer_centralizer_comm_of_comm hk _ (hc h₁) _ (hc h₂)

theorem conj_eq_inv_of_mem_closure_pair {t u w z : G} (huw : Commute u w)
    (hu : t * u * t⁻¹ = u⁻¹) (hw : t * w * t⁻¹ = w⁻¹)
    (hz : z ∈ Subgroup.closure ({u, w} : Set G)) : t * z * t⁻¹ = z⁻¹ := by
  induction hz using Subgroup.closure_induction with
  | mem z hmem =>
    rcases hmem with rfl | rfl
    · exact hu
    · exact hw
  | one => simp
  | mul z₁ z₂ hz₁ hz₂ ih₁ ih₂ =>
    calc t * (z₁ * z₂) * t⁻¹ = (t * z₁ * t⁻¹) * (t * z₂ * t⁻¹) := by group
      _ = z₁⁻¹ * z₂⁻¹ := by rw [ih₁, ih₂]
      _ = (z₁ * z₂)⁻¹ := by rw [mul_inv_rev, (commute_of_mem_closure_pair huw hz₁ hz₂).inv_inv.eq]
  | inv z hz ih =>
    calc t * z⁻¹ * t⁻¹ = (t * z * t⁻¹)⁻¹ := by group
      _ = z⁻¹⁻¹ := by rw [ih]

theorem commute_of_conj_inv_mod [Finite G] {t : G} {X L V : Subgroup G} (ht : t ^ 2 = 1)
    (hXL : X ≤ L) (hL3 : IsPGroup 3 ↥L) (hXt : ∀ g ∈ X, t * g * t⁻¹ ∈ X)
    (hV : ∀ w ∈ V, t * w * t⁻¹ = w⁻¹) (hmod : ∀ g ∈ X, t * g * t⁻¹ * g ∈ V) :
    ∀ g ∈ X, ∀ h ∈ X, g * h = h * g := by
  have ht' : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ht]
  let φ : ↥X →* ↥X :=
    { toFun := fun g => ⟨t * g * t⁻¹, hXt g g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hinv : Function.Involutive φ := fun g => Subtype.ext (by
    show t * (t * (g : G) * t⁻¹) * t⁻¹ = g
    calc t * (t * (g : G) * t⁻¹) * t⁻¹ = t * t * g * (t⁻¹ * t⁻¹) := by group
      _ = g := by rw [← pow_two, ht, ht', ← pow_two, ht, one_mul, mul_one])
  have hfix : MonoidHom.FixedPointFree φ := by
    intro g hg
    have hg' : t * (g : G) * t⁻¹ = g := congrArg Subtype.val hg
    have h1 : (g : G) ^ 2 ∈ V := by
      have := hmod g g.2
      rwa [hg', ← pow_two] at this
    have h2 : t * (g : G) ^ 2 * t⁻¹ = (g : G) ^ 2 := by
      rw [pow_two]
      calc t * ((g : G) * g) * t⁻¹ = (t * g * t⁻¹) * (t * g * t⁻¹) := by group
        _ = g * g := by rw [hg']
    have h4 : (g : G) ^ 4 = 1 := by
      have := hV _ h1
      rw [h2] at this
      calc (g : G) ^ 4 = (g : G) ^ 2 * (g : G) ^ 2 := by group
        _ = (g : G) ^ 2 * ((g : G) ^ 2)⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel _
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := hL3 ⟨g, hXL g.2⟩
    have hk' : (g : G) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime (3 ^ k) 4 := Nat.Coprime.pow_left k (by norm_num)
    have hd := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left
      (orderOf_dvd_of_pow_eq_one hk') hcop) (orderOf_dvd_of_pow_eq_one h4)
    exact Subtype.ext (orderOf_eq_one_iff.mp hd)
  intro g hg h hh
  have := hfix.commute_all_of_involutive hinv ⟨g, hg⟩ ⟨h, hh⟩
  exact congrArg Subtype.val this.eq

theorem conj_eq_inv_of_isCyclic [Finite G] {t y : G} {L V : Subgroup G} (ht : t ^ 2 = 1)
    (hL3 : IsPGroup 3 ↥L) (hyL : y ∈ L) (hy3 : orderOf y = 3) (hty : t * y * t⁻¹ = y)
    (hVL : V ≤ L) (hVt : ∀ v ∈ V, t * v * t⁻¹ ∈ V) (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hyV : y ∉ V) (hcyc : IsCyclic ↥(L ⊓ Subgroup.centralizer {t})) :
    ∀ v ∈ V, t * v * t⁻¹ = v⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht' : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht]
  set C := L ⊓ Subgroup.centralizer ({t} : Set G) with hC
  have hC3 : IsPGroup 3 ↥C := hL3.to_le inf_le_left
  have hmemC : ∀ {g : G}, g ∈ L → t * g * t⁻¹ = g → g ∈ C := fun hgL hg =>
    ⟨hgL, Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc _ = t * _ * t⁻¹ * t := by rw [hg]
        _ = t * _ := by group)⟩
  have hyC : y ∈ C := hmemC hyL hty
  intro v hv
  set w := v * (t * v * t⁻¹) with hw
  have hwV : w ∈ V := V.mul_mem hv (hVt v hv)
  have htw : t * w * t⁻¹ = w := by
    have h1 : t * (t * v * t⁻¹) * t⁻¹ = v := by
      calc t * (t * v * t⁻¹) * t⁻¹ = t * t * v * (t⁻¹ * t⁻¹) := by group
        _ = v := by rw [← pow_two, ht, ht', ← pow_two, ht, one_mul, mul_one]
    calc t * w * t⁻¹ = (t * v * t⁻¹) * (t * (t * v * t⁻¹) * t⁻¹) := by rw [hw]; group
      _ = (t * v * t⁻¹) * v := by rw [h1]
      _ = w := (hVc _ (hVt v hv) v hv)
  by_cases hw1 : w = 1
  · calc t * v * t⁻¹ = v⁻¹ * w := by rw [hw]; group
      _ = v⁻¹ := by rw [hw1, mul_one]
  · exfalso
    have hwC : w ∈ C := hmemC (hVL hwV) htw
    have hyle : Subgroup.zpowers y ≤ C := Subgroup.zpowers_le.mpr hyC
    have hwle : Subgroup.zpowers w ≤ C := Subgroup.zpowers_le.mpr hwC
    have hwVle : Subgroup.zpowers w ≤ V := Subgroup.zpowers_le.mpr hwV
    rcases A1c.le_total_of_isCyclic_isPGroup (C := C) hC3 hyle hwle with h | h
    · exact hyV (hwVle (h (Subgroup.mem_zpowers y)))
    · have hcard : Nat.card ↥(Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hy3]
      have hne : Subgroup.zpowers w ≠ ⊥ := by
        rwa [ne_eq, Subgroup.zpowers_eq_bot]
      have heq : Subgroup.zpowers w = Subgroup.zpowers y := by
        have := (Subgroup.zpowers w).subgroupOf (Subgroup.zpowers y)
        have hle' := h
        refine le_antisymm hle' ?_
        have hdvd : Nat.card ↥(Subgroup.zpowers w) ∣ 3 := hcard ▸ Subgroup.card_dvd_of_le hle'
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hne
        · exact (Subgroup.eq_of_le_of_card_ge hle' (by rw [h3, hcard])).ge
      exact hyV (hwVle (heq ▸ Subgroup.mem_zpowers y))

theorem false_of_class_three [Finite G] {x₁ x₂ a b : G} {L : Subgroup G}
    (hL : L = Subgroup.closure {x₁, x₂}) [hLn : L.Normal]
    (hx₁ : x₁ ^ 3 = 1) (hx₂ : x₂ ^ 3 = 1)
    (ha₁ : a * x₁ * a⁻¹ = x₁) (ha₂ : a * x₂ * a⁻¹ = x₂⁻¹)
    (hb₁ : b * x₁ * b⁻¹ = x₁⁻¹) (hb₂ : b * x₂ * b⁻¹ = x₂)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hL3 : IsPGroup 3 ↥L)
    (hVc : ⁅⁅L, L⁆, L⁆ ≤ Subgroup.centralizer (L : Set G)) (hVbot : ⁅⁅L, L⁆, L⁆ ≠ ⊥)
    (hca : IsCyclic ↥(L ⊓ Subgroup.centralizer {a}))
    (hcb : IsCyclic ↥(L ⊓ Subgroup.centralizer {b})) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set γ := ⁅L, L⁆ with hγdef
  set V := ⁅γ, L⁆ with hVdef
  have hγn : γ.Normal := Subgroup.commutator_normal L L
  have hVn : V.Normal := Subgroup.commutator_normal γ L
  have hVγ : V ≤ γ := Subgroup.commutator_le_left γ L
  have hγL : γ ≤ L := Subgroup.commutator_le_left L L
  have hx₁L : x₁ ∈ L := hL ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hx₂L : x₂ ∈ L := hL ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  set c := ⁅x₁, x₂⁆ with hcdef
  have hγc : γ ≤ Subgroup.zpowers c ⊔ V := by
    have := commutator_closure_pair_le x₁ x₂ V (by rw [← hL])
    rwa [← hL] at this
  have hVL : ⁅V, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hVc
  have hcV : c ∈ V → False := by
    intro hc
    have h1 : γ ≤ V := hγc.trans (sup_le (Subgroup.zpowers_le.mpr hc) le_rfl)
    apply hVbot
    exact le_bot_iff.mp (hVL ▸ Subgroup.commutator_mono h1 le_rfl)
  have hx₁γ : x₁ ∉ γ := fun h => hcV (Subgroup.commutator_mem_commutator h hx₂L)
  have hx₂γ : x₂ ∉ γ := fun h => hcV (by
    rw [hVdef, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hx₁L h)
  have hord : ∀ {x : G}, x ^ 3 = 1 → x ∉ γ → orderOf x = 3 := fun hx3 hxγ =>
    orderOf_eq_prime hx3 fun h1 => hxγ (h1 ▸ γ.one_mem)
  have hx₁3 := hord hx₁ hx₁γ
  have hx₂3 := hord hx₂ hx₂γ
  have hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    (Subgroup.mem_centralizer_iff.mp (hVc hv) w (hVγ.trans hγL hw)).symm
  have hVt : ∀ {t : G}, (∀ g ∈ L, t * g * t⁻¹ ∈ L) → ∀ v ∈ V, t * v * t⁻¹ ∈ V := by
    intro t htL v hv
    have hmap : V.map (MulAut.conj t).toMonoidHom ≤ V := by
      have hLt : L.map (MulAut.conj t).toMonoidHom ≤ L := by
        rintro _ ⟨g, hg, rfl⟩
        exact htL g hg
      rw [hVdef, hγdef, Subgroup.map_commutator, Subgroup.map_commutator]
      exact Subgroup.commutator_mono (Subgroup.commutator_mono hLt hLt) hLt
    exact hmap ⟨v, hv, rfl⟩
  have hLconj : ∀ {t : G}, t * x₁ * t⁻¹ ∈ L → t * x₂ * t⁻¹ ∈ L → ∀ g ∈ L, t * g * t⁻¹ ∈ L := by
    intro t h₁ h₂ g hg
    have : L.map (MulAut.conj t).toMonoidHom ≤ L := by
      rw [hL, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨z, hz, rfl⟩
      rcases hz with rfl | rfl
      · exact hL ▸ h₁
      · exact hL ▸ h₂
    exact this ⟨g, hg, rfl⟩
  have haL := hLconj (by rw [ha₁]; exact hx₁L) (by rw [ha₂]; exact L.inv_mem hx₂L)
  have hbL := hLconj (by rw [hb₁]; exact L.inv_mem hx₁L) (by rw [hb₂]; exact hx₂L)
  have haV := conj_eq_inv_of_isCyclic ha hL3 hx₁L hx₁3 ha₁ (hVγ.trans hγL) (hVt haL) hVab
    (fun h => hx₁γ (hVγ h)) hca
  have hbV := conj_eq_inv_of_isCyclic hb hL3 hx₂L hx₂3 hb₂ (hVγ.trans hγL) (hVt hbL) hVab
    (fun h => hx₂γ (hVγ h)) hcb
  set π := QuotientGroup.mk' V with hπ
  have hπV : ∀ g, π g = 1 ↔ g ∈ V := fun g => QuotientGroup.eq_one_iff g
  have hcent : ∀ g ∈ L, ∀ z ∈ γ, π g * π z = π z * π g := by
    intro g hg z hz
    have h1 : ⁅g, z⁆ ∈ V := by
      rw [hVdef, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hg hz
    have h2 : π ⁅g, z⁆ = 1 := (hπV _).mpr h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  have hcγ : c ∈ γ := Subgroup.commutator_mem_commutator hx₁L hx₂L
  have hmod : ∀ {t y : G}, y ∈ L → t * y * t⁻¹ = y⁻¹ → π (t * c * t⁻¹) = (π c)⁻¹ →
      ∀ g ∈ Subgroup.zpowers y ⊔ γ, t * g * t⁻¹ * g ∈ V := by
    intro t y hyL hty htc g hg
    have hyc : Commute (π y) (π c) := hcent y hyL c hcγ
    have hle : (Subgroup.zpowers y ⊔ γ).map π ≤ Subgroup.closure {π y, π c} := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _))) ?_
      refine (Subgroup.map_mono hγc).trans ?_
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, QuotientGroup.map_mk'_self, sup_bot_eq]
      exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    have hπy : π t * π y * (π t)⁻¹ = (π y)⁻¹ := by rw [← map_inv, ← map_mul, ← map_mul, hty,
      map_inv]
    have hπc : π t * π c * (π t)⁻¹ = (π c)⁻¹ := by rw [← map_inv, ← map_mul, ← map_mul, htc]
    have h1 := conj_eq_inv_of_mem_closure_pair hyc hπy hπc (hle ⟨g, hg, rfl⟩)
    rw [← hπV, map_mul, map_mul, map_mul, map_inv, h1, inv_mul_cancel]
  have hbc : π (b * c * b⁻¹) = (π c)⁻¹ := by
    have h1 : b * c * b⁻¹ = ⁅x₁⁻¹, x₂⁆ := by
      rw [hcdef, ← MulAut.conj_apply, map_commutatorElement, MulAut.conj_apply,
        MulAut.conj_apply, hb₁, hb₂]
    rw [h1, commutatorElement_inv_left', map_mul, map_mul, map_inv, map_inv, ← hcdef]
    have h2 := hcent x₁ hx₁L c hcγ
    calc (π x₁)⁻¹ * (π c)⁻¹ * π x₁ = (π x₁)⁻¹ * ((π c)⁻¹ * π x₁) := by group
      _ = (π x₁)⁻¹ * (π x₁ * (π c)⁻¹) := by
          rw [(Commute.inv_left (Commute.symm h2)).eq]
      _ = (π c)⁻¹ := by group
  have hac : π (a * c * a⁻¹) = (π c)⁻¹ := by
    have h1 : a * c * a⁻¹ = ⁅x₁, x₂⁻¹⁆ := by
      rw [hcdef, ← MulAut.conj_apply, map_commutatorElement, MulAut.conj_apply,
        MulAut.conj_apply, ha₁, ha₂]
    rw [h1, commutatorElement_inv_right', map_mul, map_mul, map_inv, map_inv, ← hcdef]
    have h2 := hcent x₂ hx₂L c hcγ
    calc (π x₂)⁻¹ * (π c)⁻¹ * π x₂ = (π x₂)⁻¹ * ((π c)⁻¹ * π x₂) := by group
      _ = (π x₂)⁻¹ * (π x₂ * (π c)⁻¹) := by
          rw [(Commute.inv_left (Commute.symm h2)).eq]
      _ = (π c)⁻¹ := by group
  have hpres : ∀ {t y : G}, t * y * t⁻¹ = y⁻¹ → ∀ g ∈ Subgroup.zpowers y ⊔ γ,
      t * g * t⁻¹ ∈ Subgroup.zpowers y ⊔ γ := by
    intro t y hty g hg
    have h1 : (Subgroup.zpowers y ⊔ γ).map (MulAut.conj t).toMonoidHom ≤
        Subgroup.zpowers y ⊔ γ := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      refine sup_le_sup ?_ ?_
      · rw [Subgroup.zpowers_le]
        show t * y * t⁻¹ ∈ Subgroup.zpowers y
        rw [hty]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y)
      · rintro _ ⟨z, hz, rfl⟩
        exact hγn.conj_mem z hz t
    exact h1 ⟨g, hg, rfl⟩
  have hX₁L : Subgroup.zpowers x₁ ⊔ γ ≤ L := sup_le (Subgroup.zpowers_le.mpr hx₁L) hγL
  have hX₂L : Subgroup.zpowers x₂ ⊔ γ ≤ L := sup_le (Subgroup.zpowers_le.mpr hx₂L) hγL
  have hX₁ := commute_of_conj_inv_mod hb hX₁L hL3 (hpres hb₁) hbV (hmod hx₁L hb₁ hbc)
  have hX₂ := commute_of_conj_inv_mod ha hX₂L hL3 (hpres ha₂) haV (hmod hx₂L ha₂ hac)
  have hγcent : γ ≤ Subgroup.centralizer (L : Set G) := by
    intro z hz
    rw [hL, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro w (rfl | rfl)
    · exact hX₁ _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) z (Subgroup.mem_sup_right hz)
    · exact hX₂ _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) z (Subgroup.mem_sup_right hz)
  exact hVbot (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hγcent)

end ClassThree

end F6

end CFSG.Quasithin
