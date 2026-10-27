module

public import CFSG.Walter.Bender1970.S2.PSL2Overgroups
public import CFSG.Walter.Bender1970.S2.Inner
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
public import CFSG.Walter.JRFacts

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped MatrixGroups

@[expose] def InvolutionCentralizersGenerate (L : Type*) [Group L] : Prop :=
  ∀ u v : L, orderOf u = 2 → orderOf v = 2 → u ≠ v →
    Subgroup.centralizer ({u} : Set L) ⊔ Subgroup.centralizer ({v} : Set L) = ⊤

theorem InvolutionCentralizersGenerate.of_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : InvolutionCentralizersGenerate A) : InvolutionCentralizersGenerate B := by
  intro u v hu hv huv
  have h1 := h (e.symm u) (e.symm v) (by rwa [MulEquiv.orderOf_eq])
    (by rwa [MulEquiv.orderOf_eq]) (fun h' => huv (e.symm.injective h'))
  have h2 := congrArg (Subgroup.map e.toMonoidHom) h1
  rwa [Subgroup.map_sup, map_centralizer_singleton_mulEquiv, map_centralizer_singleton_mulEquiv,
    MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    Subgroup.map_top_of_surjective _ e.surjective] at h2

theorem centralizer_sup_centralizer_eq_top {L : Type*} [Group L] [Finite L] {u v : L}
    (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u ≠ v)
    (hmax : IsCoatom (Subgroup.centralizer ({u} : Set L))) (hconj : IsConj u v)
    (hZu : (Subgroup.center (Subgroup.centralizer ({u} : Set L))).map
      (Subgroup.centralizer ({u} : Set L)).subtype = Subgroup.zpowers u)
    (hZv : (Subgroup.center (Subgroup.centralizer ({v} : Set L))).map
      (Subgroup.centralizer ({v} : Set L)).subtype = Subgroup.zpowers v) :
    Subgroup.centralizer ({u} : Set L) ⊔ Subgroup.centralizer ({v} : Set L) = ⊤ := by
  rcases hmax.le_iff.mp (le_sup_left : Subgroup.centralizer ({u} : Set L) ≤ _) with h | h
  · exact h
  · exfalso
    have hle : Subgroup.centralizer ({v} : Set L) ≤ Subgroup.centralizer ({u} : Set L) :=
      h ▸ le_sup_right
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hcard : Nat.card (Subgroup.centralizer ({v} : Set L)) =
        Nat.card (Subgroup.centralizer ({u} : Set L)) := by
      rw [← hg, centralizer_conj_eq_map]
      exact Nat.card_congr ((MulAut.conj g).subgroupMap _).toEquiv.symm
    have heq : Subgroup.centralizer ({v} : Set L) = Subgroup.centralizer ({u} : Set L) :=
      Subgroup.eq_of_le_of_card_ge hle hcard.ge
    rw [heq] at hZv
    have hvu : v ∈ Subgroup.zpowers u := by
      rw [← hZu, hZv]
      exact Subgroup.mem_zpowers v
    have hv1 : v ≠ 1 := by rintro rfl; simp at hv
    rcases eq_one_or_eq_of_mem_zpowers hu hvu with h1 | h1
    · exact hv1 h1
    · exact huv h1.symm

theorem psl2_involutionCentralizersGenerate
    {p f : ℕ} [Fact p.Prime] (hp : Odd p) (hf : 0 < f)
    (h11 : 11 ≤ p ^ f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) :
    InvolutionCentralizersGenerate PSL(2, GaloisField p f) := by
  intro u v hu hv huv
  exact centralizer_sup_centralizer_eq_top hu hv huv
    (psl2_odd_centralizer_involution_isCoatom hp hf h11 h8 hu)
    (psl2_odd_isConj_of_orderOf_eq_two hp hf hu hv)
    (psl2_odd_center_centralizer_involution hp hf (by omega) hu)
    (psl2_odd_center_centralizer_involution hp hf (by omega) hv)

theorem IsTypeJR.involutionCentralizersGenerate {L : Type} [Group L] [Finite L]
    (hL : IsTypeJR L) : InvolutionCentralizersGenerate L := by
  intro u v hu hv huv
  exact centralizer_sup_centralizer_eq_top hu hv huv (hL.2.2 u hu).1
    (hL.isConj_of_orderOf_eq_two hu hv) (hL.center_centralizer hu) (hL.center_centralizer hv)

theorem involutionCentralizersGenerate_of_not_even
    {L : Type} [Group L] [Finite L]
    (hL : IsTypeL2 L ∨ IsTypeJR L) (h2 : ¬ IsTypeL2Even L) :
    InvolutionCentralizersGenerate L := by
  rcases hL with (heL | ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e⟩⟩) | hL
  · exact absurd heL h2
  · by_cases h11 : 11 ≤ p ^ f
    · exact (psl2_involutionCentralizersGenerate hpodd hf h11 h8).of_mulEquiv e.symm
    · exact absurd (isTypeL2Even_of_mulEquiv_psl2_five hf (by omega) e) h2
  · exact hL.involutionCentralizersGenerate

theorem bender1970_2_6
    {X : Type} [Group X] [Finite X] (hX : IsAStar X) {U : Subgroup X}
    (hU : IsKleinFour U) {E : Subgroup X} (hE : IsComponentOf E ⊤)
    (hE2 : ¬ IsTypeL2Even (E ⧸ Subgroup.center E)) :
    E = ⨆ (s : X) (_ : s ∈ U) (_ : s ≠ 1), E ⊓ Subgroup.centralizer ({s} : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hU
  set W := ⨆ (s : X) (_ : s ∈ U) (_ : s ≠ 1), E ⊓ Subgroup.centralizer ({s} : Set X) with hW
  have hWE : W ≤ E := iSup₂_le fun s _ => iSup_le fun _ => inf_le_left
  have hsW : ∀ s ∈ U, s ≠ 1 → E ⊓ Subgroup.centralizer ({s} : Set X) ≤ W := fun s hs hs1 =>
    le_iSup₂_of_le (f := fun s (_ : s ∈ U) => ⨆ (_ : s ≠ 1),
      E ⊓ Subgroup.centralizer ({s} : Set X)) s hs (le_iSup_of_le hs1 le_rfl)
  refine le_antisymm ?_ hWE
  by_cases hcent : ∃ s ∈ U, s ≠ 1 ∧ E ≤ Subgroup.centralizer ({s} : Set X)
  · obtain ⟨s, hs, hs1, hEs⟩ := hcent
    exact (le_inf le_rfl hEs).trans (hsW s hs hs1)
  push Not at hcent
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  have hsq : ∀ s ∈ U, s * s = 1 := fun s hs =>
    congrArg Subtype.val (IsKleinFour.mul_self (⟨s, hs⟩ : U))
  have hinner : ∀ s ∈ U, ∃ k ∈ E, ∀ x ∈ E, s * x * s⁻¹ = k * x * k⁻¹ := fun s hs =>
    exists_inner_of_isPGroup hX.1 hU2 hE hs
  obtain ⟨a, ha, ha1, b, hb, hb1, hab⟩ : ∃ a ∈ U, a ≠ 1 ∧ ∃ b ∈ U, b ≠ 1 ∧ a ≠ b := by
    have := Fintype.ofFinite U
    have : Nontrivial U := by
      rw [← Finite.one_lt_card_iff_nontrivial, IsKleinFour.card_four]
      norm_num
    obtain ⟨⟨a, ha⟩, ha1⟩ := exists_ne (1 : U)
    refine ⟨a, ha, fun h => ha1 (Subtype.ext h), ?_⟩
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset U) ⊆ {1, ⟨a, ha⟩} := by
      intro y _
      by_cases hy : (y : X) = 1
      · rw [Finset.mem_insert]
        exact Or.inl (Subtype.ext hy)
      · rw [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Subtype.ext (hcon y y.2 hy).symm)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, IsKleinFour.card_four'] at h1
    have h2 := Finset.card_le_two (a := (1 : U)) (b := ⟨a, ha⟩)
    omega
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    have h' : b = a⁻¹ := (eq_inv_of_mul_eq_one_right h)
    rw [h', inv_eq_of_mul_eq_one_right (hsq a ha)]
  obtain ⟨ka, hka, hkaconj⟩ := hinner a ha
  obtain ⟨kb, hkb, hkbconj⟩ := hinner b hb
  set Z := Subgroup.center E with hZdef
  set π : E →* E ⧸ Z := QuotientGroup.mk' Z with hπ
  have hZodd : Odd (Nat.card Z) := odd_card_center_of_isQuasisimple hE.2.2 (hX.1.subgroup E)
  have htriv : ∀ s : X, ∀ k (hk : k ∈ E), (∀ x ∈ E, s * x * s⁻¹ = k * x * k⁻¹) →
      π ⟨k, hk⟩ = 1 → E ≤ Subgroup.centralizer ({s} : Set X) := fun s k hk hsk h1 =>
    le_centralizer_of_mk_eq_one hk hsk h1
  have hinv : ∀ s ∈ U, s ≠ 1 → ∀ k (hk : k ∈ E), (∀ x ∈ E, s * x * s⁻¹ = k * x * k⁻¹) →
      orderOf (π ⟨k, hk⟩) = 2 := fun s hs hs1 k hk hsk =>
    orderOf_mk_eq_two_of_inner (hsq s hs) hk hsk (hcent s hs hs1)
  set ua : E ⧸ Z := π ⟨ka, hka⟩ with hua
  set ub : E ⧸ Z := π ⟨kb, hkb⟩ with hub
  have hua2 := hinv a ha ha1 ka hka hkaconj
  have hub2 := hinv b hb hb1 kb hkb hkbconj
  have huab : ua ≠ ub := by
    intro h
    have habconj : ∀ x ∈ E, (a * b) * x * (a * b)⁻¹ = (ka * kb) * x * (ka * kb)⁻¹ := by
      intro x hx
      have hm : kb * x * kb⁻¹ ∈ E := E.mul_mem (E.mul_mem hkb hx) (E.inv_mem hkb)
      calc (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
        _ = a * (kb * x * kb⁻¹) * a⁻¹ := by rw [hkbconj x hx]
        _ = ka * (kb * x * kb⁻¹) * ka⁻¹ := hkaconj _ hm
        _ = (ka * kb) * x * (ka * kb)⁻¹ := by group
    have h1 : π ⟨ka * kb, E.mul_mem hka hkb⟩ = 1 := by
      have : (⟨ka * kb, E.mul_mem hka hkb⟩ : E) = ⟨ka, hka⟩ * ⟨kb, hkb⟩ := rfl
      rw [this, map_mul, ← hua, ← hub, ← h, ← pow_two, ← hua2, pow_orderOf_eq_one]
    exact hcent (a * b) (U.mul_mem ha hb) hab1 (htriv (a * b) (ka * kb) _ habconj h1)
  have hgen : InvolutionCentralizersGenerate (E ⧸ Z) :=
    involutionCentralizersGenerate_of_not_even (hX.isTypeL2_or_isTypeJR hE) hE2
  have htop := hgen ua ub hua2 hub2 huab
  have hlift : ∀ s ∈ U, ∀ k (hk : k ∈ E), (∀ x ∈ E, s * x * s⁻¹ = k * x * k⁻¹) →
      ((Subgroup.centralizer ({s} : Set X)).subgroupOf E).map π =
        Subgroup.centralizer ({π ⟨k, hk⟩} : Set (E ⧸ Z)) := by
    intro s hs k hk hsk
    have hcomap : (Subgroup.centralizer ({s} : Set X)).subgroupOf E =
        (Subgroup.centralizer ({π ⟨k, hk⟩} : Set (E ⧸ Z))).comap π := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      exact mem_centralizer_iff_of_inner hZodd (hsq s hs) hk hsk x
    rw [hcomap, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z)]
  set Ca := (Subgroup.centralizer ({a} : Set X)).subgroupOf E with hCa
  set Cb := (Subgroup.centralizer ({b} : Set X)).subgroupOf E with hCb
  have hsup : (Ca ⊔ Cb) ⊔ Z = ⊤ := by
    have h1 : (Ca ⊔ Cb).map π = ⊤ := by
      rw [Subgroup.map_sup, hlift a ha ka hka hkaconj, hlift b hb kb hkb hkbconj]
      exact htop
    have h2 := congrArg (Subgroup.comap π) h1
    rwa [Subgroup.comap_map_eq, Subgroup.comap_top, hπ, QuotientGroup.ker_mk'] at h2
  have hCab : Ca ⊔ Cb = ⊤ := eq_top_of_sup_center_eq_top hE.2.2.2.1 hsup
  intro x hx
  have hx' : (⟨x, hx⟩ : E) ∈ Ca ⊔ Cb := hCab ▸ Subgroup.mem_top _
  have hle : (Ca ⊔ Cb).map E.subtype ≤ W := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hsW a ha ha1 ⟨y.2, hy⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hsW b hb hb1 ⟨y.2, hy⟩
  exact hle ⟨⟨x, hx⟩, hx', rfl⟩

theorem isKleinFour_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsKleinFour A) : IsKleinFour B :=
  ⟨(Nat.card_congr e.toEquiv).symm.trans h.card_four,
    (Monoid.exponent_eq_of_mulEquiv e).symm.trans h.exponent_two⟩

theorem bender1970_2_6_subgroup
    {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsAStar H) {U : Subgroup G} (hUH : U ≤ H) (hU : IsKleinFour U) {E : Subgroup G}
    (hE : IsComponentOf E H) (hE2 : ¬ IsTypeL2Even (E ⧸ Subgroup.center E)) :
    E = ⨆ (s : G) (_ : s ∈ U) (_ : s ≠ 1), E ⊓ Subgroup.centralizer ({s} : Set G) := by
  set U' := U.subgroupOf H
  set E' := E.subgroupOf H
  let eE : E' ≃* E := Subgroup.subgroupOfEquivOfLe hE.1
  have hU' : IsKleinFour U' := isKleinFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hUH).symm hU
  have hE' : IsComponentOf E' ⊤ := fstar_isComponentOf_subgroupOf_top hE
  have hE2' : ¬ IsTypeL2Even (E' ⧸ Subgroup.center E') := by
    rintro ⟨f, hf, ⟨φ⟩⟩
    exact hE2 ⟨f, hf, ⟨(QuotientGroup.congr _ _ eE (Subgroup.map_center_eq eE)).symm.trans φ⟩⟩
  have hmain := bender1970_2_6 hH hU' hE' hE2'
  refine le_antisymm ?_ (iSup₂_le fun s _ => iSup_le fun _ => inf_le_left)
  intro x hx
  have hx' : (⟨x, hE.1 hx⟩ : H) ∈ E' := hx
  rw [hmain] at hx'
  have hle : (⨆ (s : H) (_ : s ∈ U') (_ : s ≠ 1),
      E' ⊓ Subgroup.centralizer ({s} : Set H)).map H.subtype ≤
      ⨆ (s : G) (_ : s ∈ U) (_ : s ≠ 1), E ⊓ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun s => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hs => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hs1 => ?_
    have hsU : (s : G) ∈ U := hs
    have hs1' : (s : G) ≠ 1 := fun h => hs1 (Subtype.ext h)
    refine le_trans ?_ (le_iSup₂_of_le (f := fun (t : G) (_ : t ∈ U) => ⨆ (_ : t ≠ 1),
      E ⊓ Subgroup.centralizer ({t} : Set G)) (s : G) hsU (le_iSup_of_le hs1' le_rfl))
    rintro _ ⟨y, ⟨hyE, hyC⟩, rfl⟩
    refine ⟨hyE, ?_⟩
    have hyC' : y ∈ Subgroup.centralizer ({s} : Set H) := hyC
    show (y : G) ∈ Subgroup.centralizer ({(s : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC' ⊢
    exact congrArg Subtype.val hyC'
  exact hle ⟨_, hx', rfl⟩

end CFSG.Walter
