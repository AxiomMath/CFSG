module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndStarComp

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndZWr
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_KernelT
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.Quasithin.Background.BlueprintB2Frattini

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

@[expose] def KFactE27SignalizerOne : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P A : Subgroup X), CFSG.Open.IsKGroup X →
    UC22.InS3.UC327.Hyp327 X P A → Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1) →
    CFSG.pPrimeCore 3 X = ⊥ →
    (∀ a ∈ A, a ≠ 1 → ∀ W : Subgroup X, W ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({a} : Set X))) →
    ∀ L : Subgroup X, CFSG.IsComponent L → CFSG.layer X = L →
      P ⊓ Subgroup.centralizer (L : Set X) ≤ Subgroup.centralizer (P : Set X) →
    ∀ W : Subgroup X, A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W ≤ Subgroup.centralizer (L : Set X)

namespace A10Gen

variable {X : Type} [Group X] [Finite X]

theorem exists_mem_inf_not_mem_centralizer_of_isComponent {P L : Subgroup X}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hL : CFSG.IsComponent L) : ∃ x ∈ P ⊓ L, x ∉ Subgroup.centralizer (L : Set X) := by
  classical
  have hLne : L ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot L).mp (CFSG.LocalCores.isQuasisimple_nontrivial hL.1)
  have h3dvd : 3 ∣ Nat.card L := by
    by_contra h
    have hcop : Nat.Coprime 3 (Nat.card L) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h
    have hle := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hL.2 hcop
    rw [h3'] at hle
    exact hLne (le_bot_iff.mp hle)
  have hLlay : L ≤ CFSG.layer X := CFSG.LocalCores.component_le_layer hL
  have hLnorm : CFSG.layer X ≤ Subgroup.normalizer (L : Set X) :=
    CFSG.LocalCores.layer_le_normalizer hL
  haveI hchar : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI : (CFSG.layer X).Normal := Subgroup.normal_of_characteristic _
  have hsylL : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ CFSG.layer X) (CFSG.layer X) :=
    hP.inf_of_le_normalizer le_top (by
      rw [Subgroup.normalizer_eq_top (CFSG.layer X)])
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 ((P ⊓ CFSG.layer X) ⊓ L) L :=
    hsylL.inf_of_le_normalizer hLlay hLnorm
  rw [inf_assoc, inf_eq_right.mpr hLlay] at hsyl
  obtain ⟨Q, hQ⟩ := hsyl.exists_sylow_eq_subgroupOf
  obtain ⟨x, hxQ, hxcent⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116t_exists_noncentral_pElt
      (⟨hL.1.1.commutator_eq_top, hL.1.2.1⟩ : CFSG.Open.IsQuasisimple ↥L)
      Nat.prime_three Q h3dvd
  refine ⟨(x : X), ?_, ?_⟩
  · have hx : x ∈ (P ⊓ L).subgroupOf L := hQ ▸ hxQ
    exact Subgroup.mem_subgroupOf.mp hx
  · intro hxc
    refine hxcent ((Subgroup.mem_center_iff).mpr fun y => Subtype.ext ?_)
    exact Subgroup.mem_centralizer_iff.mp hxc (y : X) y.2

private lemma le_centralizer_of_isComponent_of_ne {K L : Subgroup X}
    (hK : CFSG.IsComponent K) (hL : CFSG.IsComponent L) (hne : K ≠ L) :
    K ≤ Subgroup.centralizer (L : Set X) := by
  rcases CFSG.LocalCores.distinct_components_commute hK hL with h | h
  · exact absurd h hne
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

private lemma mulEquiv_mem_centralizer_map {L : Subgroup X} (e : X ≃* X) {y : X}
    (hy : y ∈ Subgroup.centralizer (L : Set X)) :
    e y ∈ Subgroup.centralizer ((L.map e.toMonoidHom : Subgroup X) : Set X) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro l' hl'
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hl'
  calc e l * e y = e (l * y) := (map_mul e l y).symm
    _ = e (y * l) := by rw [hy l hl]
    _ = e y * e l := map_mul e y l

private lemma mem_centralizer_map_mulEquiv_iff {L : Subgroup X} (e : X ≃* X) (y : X) :
    y ∈ Subgroup.centralizer ((L.map e.toMonoidHom : Subgroup X) : Set X) ↔
      e.symm y ∈ Subgroup.centralizer (L : Set X) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h l hl
    have h1 := h (e l) (Subgroup.mem_map_of_mem _ hl)
    have h2 := congrArg e.symm h1
    simpa only [map_mul, MulEquiv.symm_apply_apply] using h2
  · intro h l' hl'
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hl'
    have h1 := h l hl
    show e.toMonoidHom l * y = y * e.toMonoidHom l
    simpa only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply] using congrArg e h1

private lemma exists_conj_setup_of_not_mem_normalizer {P A L : Subgroup X}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hAP : A ≤ P)
    (hAn : P ≤ Subgroup.normalizer (A : Set X)) (hL : CFSG.IsComponent L)
    {a : X} (haA : a ∈ A) (haN : a ∉ Subgroup.normalizer (L : Set X)) :
    ∃ (x : X) (L' : Subgroup X) (x1 x2 : X),
      CFSG.IsComponent L' ∧ L' = L.map (MulAut.conj a⁻¹).toMonoidHom ∧ L' ≠ L ∧
      x ∈ P ⊓ L ∧ x ∉ Subgroup.centralizer (L : Set X) ∧
      x ∈ Subgroup.centralizer (L' : Set X) ∧
      x1 = (MulAut.conj a⁻¹) x ∧ x2 = (MulAut.conj a⁻¹) x1 ∧
      x1 ∈ Subgroup.centralizer (L : Set X) ∧
      x2 ∈ Subgroup.centralizer (L' : Set X) ∧ x1 * x = x * x1 := by
  classical
  let c : X ≃* X := MulAut.conj a⁻¹
  let L' : Subgroup X := L.map c.toMonoidHom
  have hL' : CFSG.IsComponent L' := CFSG.LocalCores.isComponent_map_mulEquiv c hL
  have hL'def : L' = Subgroup.map c.toMonoidHom L := rfl
  have hL'ne : L' ≠ L := by
    intro h
    apply haN
    have hm : Subgroup.map c.toMonoidHom L = L := hL'def ▸ h
    have hcs : Subgroup.map c.symm.toMonoidHom L = L := by
      calc Subgroup.map c.symm.toMonoidHom L
          = Subgroup.map c.symm.toMonoidHom (Subgroup.map c.toMonoidHom L) := by rw [hm]
        _ = L := by rw [Subgroup.map_map]; simp
    have h3 : Subgroup.map (MulAut.conj a).toMonoidHom L = L := by
      simpa [c] using hcs
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mpr h3
  have hcentL' : L ≤ Subgroup.centralizer (L' : Set X) :=
    le_centralizer_of_isComponent_of_ne hL hL' (Ne.symm hL'ne)
  have hcentL : L' ≤ Subgroup.centralizer (L : Set X) :=
    le_centralizer_of_isComponent_of_ne hL' hL hL'ne
  obtain ⟨x, hxPL, hxC⟩ := exists_mem_inf_not_mem_centralizer_of_isComponent hP h3' hL
  have hxL : x ∈ L := hxPL.2
  have hxcentL' : x ∈ Subgroup.centralizer (L' : Set X) := hcentL' hxL
  have hx1mem : c x ∈ L' := Subgroup.mem_map_of_mem c.toMonoidHom hxL
  have hx1cent : c x ∈ Subgroup.centralizer (L : Set X) := hcentL hx1mem
  have hx2cent : c (c x) ∈ Subgroup.centralizer (L' : Set X) := by
    have := mulEquiv_mem_centralizer_map (L := L) c hx1cent
    simpa [L'] using this
  refine ⟨x, L', c x, c (c x), hL', ?_, hL'ne, hxPL, hxC, hxcentL', rfl, rfl,
    hx1cent, hx2cent, ?_⟩
  · simp [L', c]
  · exact (Subgroup.mem_centralizer_iff.mp hxcentL') (c x) hx1mem

private lemma key_eq_of_conj_setup {P A : Subgroup X} {a x x1 x2 : X}
    (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAn : P ≤ Subgroup.normalizer (A : Set X)) (haA : a ∈ A) (hxP : x ∈ P)
    (hx1eq : x1 = (MulAut.conj a⁻¹) x)
    (hx2eq : x2 = (MulAut.conj a⁻¹) x1) :
    x1⁻¹ * x2 = x⁻¹ * x1 := by
  let y : X := x⁻¹ * x1
  have hyA : y ∈ A := by
    have h1 : x⁻¹ * a⁻¹ * x ∈ A := by
      have hxinv : x⁻¹ ∈ P := P.inv_mem hxP
      have hnorm := hAn hxinv
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hnorm
      have hmem : (MulAut.conj x⁻¹) a⁻¹ ∈ A := by
        rw [← hnorm]
        exact Subgroup.mem_map_of_mem _ (A.inv_mem haA)
      simpa [MulAut.conj_apply] using hmem
    have h2 : (x⁻¹ * a⁻¹ * x) * a ∈ A := A.mul_mem h1 haA
    change x⁻¹ * x1 ∈ A
    rw [hx1eq]
    simpa [MulAut.conj_apply, mul_assoc] using h2
  have hcommA : a⁻¹ * y * a = y := by
    have hcomm := congrArg Subtype.val
      (hA.1.is_comm.comm (⟨a⁻¹, A.inv_mem haA⟩ : ↥A) ⟨y, hyA⟩)
    simp only [Subgroup.coe_mul] at hcomm
    calc a⁻¹ * y * a = y * a⁻¹ * a := by rw [hcomm]
      _ = y := by group
  calc x1⁻¹ * x2 = a⁻¹ * x⁻¹ * x1 * a := by
        rw [hx2eq, hx1eq]
        simp only [MulAut.conj_apply, inv_inv]
        group
    _ = a⁻¹ * y * a := by simp only [y]; group
    _ = y := hcommA
    _ = x⁻¹ * x1 := rfl

private lemma sq_mem_centralizer_of_key_eq {L L' : Subgroup X} {a x x1 x2 : X}
    (hL'def : L' = L.map (MulAut.conj a⁻¹).toMonoidHom)
    (hx1eq : x1 = (MulAut.conj a⁻¹) x)
    (hx1cent : x1 ∈ Subgroup.centralizer (L : Set X))
    (hx2cent : x2 ∈ Subgroup.centralizer (L' : Set X))
    (hxcent : x ∈ Subgroup.centralizer (L' : Set X)) (hxcomm : x1 * x = x * x1)
    (hkey : x1⁻¹ * x2 = x⁻¹ * x1) :
    x ^ 2 ∈ Subgroup.centralizer (L : Set X) := by
  have hxsq : x * x2 = x1 ^ 2 := by
    calc x * x2 = x * (x1 * (x1⁻¹ * x2)) := by group
      _ = x * (x1 * (x⁻¹ * x1)) := by rw [hkey]
      _ = (x * x1) * (x⁻¹ * x1) := by group
      _ = (x1 * x) * (x⁻¹ * x1) := by rw [← hxcomm]
      _ = x1 ^ 2 := by rw [pow_two]; group
  have hx1sq : x1 ^ 2 ∈ Subgroup.centralizer (L' : Set X) := by
    rw [← hxsq]
    exact Subgroup.mul_mem _ hxcent hx2cent
  have h := (mem_centralizer_map_mulEquiv_iff (L := L)
    (MulAut.conj a⁻¹) (x1 ^ 2)).mp (by simpa [hL'def] using hx1sq)
  rw [show (MulAut.conj a⁻¹).symm (x1 ^ 2) = x ^ 2 by
    rw [hx1eq]
    simp only [map_pow, MulEquiv.symm_apply_apply]] at h
  exact h

private lemma exists_sq_mem_centralizer_of_not_mem_normalizer {P A L : Subgroup X}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hAP : A ≤ P)
    (hAn : P ≤ Subgroup.normalizer (A : Set X)) (hL : CFSG.IsComponent L)
    {a : X} (haA : a ∈ A) (haN : a ∉ Subgroup.normalizer (L : Set X)) :
    ∃ x ∈ P ⊓ L, x ∉ Subgroup.centralizer (L : Set X) ∧
      x ^ 2 ∈ Subgroup.centralizer (L : Set X) := by
  obtain ⟨x, L', x1, x2, -, hL'def, -, hxPL, hxC, hxcentL', hx1eq, hx2eq,
    hx1cent, hx2cent, hxcomm⟩ :=
    exists_conj_setup_of_not_mem_normalizer hP h3' hA hAP hAn hL haA haN
  have hkey := key_eq_of_conj_setup hA hAn haA hxPL.1 hx1eq hx2eq
  exact ⟨x, hxPL, hxC, sq_mem_centralizer_of_key_eq hL'def hx1eq hx1cent hx2cent
    hxcentL' hxcomm hkey⟩

theorem le_normalizer_of_isComponent {P A L : Subgroup X}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hAP : A ≤ P)
    (hAn : P ≤ Subgroup.normalizer (A : Set X)) (hL : CFSG.IsComponent L) :
    A ≤ Subgroup.normalizer (L : Set X) := by
  classical
  by_contra hcon
  obtain ⟨a, haA, haN⟩ := Set.not_subset.mp hcon
  obtain ⟨x, hxPL, hxC, hx2centL⟩ :=
    exists_sq_mem_centralizer_of_not_mem_normalizer hP h3' hA hAP hAn hL haA haN
  have hxP : x ∈ P := hxPL.1
  have hxp : x ∈ Subgroup.zpowers (x ^ 2) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP.isPGroup) (⟨x, hxP⟩ : ↥P)
    have hn' : orderOf x = 3 ^ n := by simpa using hn
    have hcop : Nat.Coprime 2 (orderOf x) := by
      rw [hn']
      exact Nat.Coprime.pow_right n (by norm_num)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    exact Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), by rw [zpow_natCast]; exact hm⟩
  exact hxC (Subgroup.zpowers_le.mpr hx2centL hxp)

private lemma mulAut_conj_mem_of_le_normalizer {R Q : Subgroup X}
    (hQR : Q ≤ Subgroup.normalizer (R : Set X)) {g : X} (hg : g ∈ Q) {x : X}
    (hx : x ∈ R) : (MulAut.conj g) x ∈ R := by
  have hmap : Subgroup.map (MulAut.conj g).toMonoidHom R = R :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hQR hg)
  exact hmap ▸ Subgroup.mem_map_of_mem _ hx

private lemma map_conj_map_conj_inv (M : Subgroup X) (g : X) :
    Subgroup.map (MulAut.conj g).toMonoidHom
      (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom M) = M := by
  rw [Subgroup.map_conj_map_conj]
  have hhom : MulAut.conj (g * g⁻¹) = (1 : X ≃* X) := by simp
  rw [hhom]
  have h1 : ((1 : X ≃* X).toMonoidHom : X →* X) = MonoidHom.id X := by ext x; simp
  rw [h1, Subgroup.map_id]

private lemma sup_zpowers_eq_of_relIndex_three {A B : Subgroup X} (hAB : A ≤ B)
    (hidx : A.relIndex B = 3) {x : X} (hxB : x ∈ B) (hxA : x ∉ A) :
    A ⊔ Subgroup.zpowers x = B := by
  let C : Subgroup X := A ⊔ Subgroup.zpowers x
  have hAC : A ≤ C := le_sup_left
  have hCB : C ≤ B := sup_le hAB (Subgroup.zpowers_le.mpr hxB)
  have hCne : A.relIndex C ≠ 1 := by
    intro h
    exact hxA (Subgroup.relIndex_eq_one.mp h (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  have hdvd : A.relIndex C ∣ A.relIndex B :=
    ⟨C.relIndex B, (Subgroup.relIndex_mul_relIndex A C B hAC hCB).symm⟩
  rw [hidx] at hdvd
  have hC3 : A.relIndex C = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd h1 hCne
    · exact h3
  have hCB1 : C.relIndex B = 1 := by
    have h := Subgroup.relIndex_mul_relIndex A C B hAC hCB
    rw [hC3, hidx] at h
    omega
  exact le_antisymm hCB (Subgroup.relIndex_eq_one.mp hCB1)

private lemma mem_zpowers_of_pow_three_of_isCyclic {B : Subgroup X}
    (hB : ∀ x ∈ B, x ^ 3 = 1) (hcyc : IsCyclic ↥B)
    {u v : X} (hu : u ∈ B) (hu1 : u ≠ 1) (hv : v ∈ B) (hv1 : v ≠ 1) :
    v ∈ Subgroup.zpowers u := by
  classical
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgtop : Subgroup.zpowers g = ⊤ := eq_top_iff.mpr fun x _ => hg x
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hB (g : X) g.2)
  have hcardB : Nat.card ↥B = 3 := by
    have hcard : Nat.card ↥B = orderOf g := by
      rw [← Nat.card_zpowers (a := g), hgtop, Subgroup.card_top]
    rw [hcard]
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hg3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      have hg1 : g = 1 := orderOf_eq_one_iff.mp h1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨u, hu⟩)
      rw [hg1, one_zpow] at hk
      exact hu1 (congrArg Subtype.val hk.symm)
    · exact h3
  have hcardu : Nat.card ↥(Subgroup.zpowers (⟨u, hu⟩ : ↥B)) = 3 := by
    rw [Nat.card_zpowers]
    have hdvd : orderOf (⟨u, hu⟩ : ↥B) ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact Subtype.ext (by simpa using hB u hu)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      exact hu1 (by simpa using congrArg Subtype.val (orderOf_eq_one_iff.mp h1))
    · exact h3
  have htopu : Subgroup.zpowers (⟨u, hu⟩ : ↥B) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hcardu, hcardB])
  have hv' : (⟨v, hv⟩ : ↥B) ∈ Subgroup.zpowers (⟨u, hu⟩ : ↥B) := by
    rw [htopu]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv'
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
    have := congrArg (fun z : ↥B => (z : X)) hk
    simpa using this⟩

private lemma le_and_relIndex_of_hyp327 {P A : Subgroup X}
    (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) :
    A ≤ P ∧ P ≤ Subgroup.normalizer (A : Set X) ∧ A.relIndex P = 3 ∧
      Nat.card P = 81 := by
  classical
  have hAP : A ≤ P := by
    rw [hX.jA]
    exact Subgroup.map_subtype_le _
  have hAn : P ≤ Subgroup.normalizer (A : Set X) := by
    rw [hX.jA]
    exact CFSG.Quasithin.BlueprintB2.le_normalizer_map_elemThompson (p := 3) P
  have hcardP : Nat.card P = 81 := by
    obtain ⟨e⟩ := hPZ
    rw [Nat.card_congr e.toEquiv]
    simpa using (CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.zwr_card_center_Zwr
      (n := 1) (by norm_num)).1
  have hrelidx : A.relIndex P = 3 := by
    have h1 : A.relIndex P * Nat.card A = Nat.card P := by
      have := Subgroup.relIndex_mul_card A P
      rwa [inf_eq_left.mpr hAP] at this
    rw [hX.card, hcardP] at h1
    omega
  exact ⟨hAP, hAn, hrelidx, hcardP⟩

private lemma inf_normalizer_eq_of_not_le_normalizer {P A L : Subgroup X}
    (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1))
    (h3' : CFSG.pPrimeCore 3 X = ⊥) (hL : CFSG.IsComponent L)
    (hPL : ¬ P ≤ Subgroup.normalizer (L : Set X)) :
    P ⊓ Subgroup.normalizer (L : Set X) = A := by
  classical
  obtain ⟨hAP, hAn, hrelidx, -⟩ := le_and_relIndex_of_hyp327 hX hPZ
  have hAL : A ≤ Subgroup.normalizer (L : Set X) :=
    le_normalizer_of_isComponent hX.sylow h3' hX.elem hAP hAn hL
  refine le_antisymm ?_ (le_inf hAP hAL)
  intro x hx
  by_contra hxA
  have hmax := sup_zpowers_eq_of_relIndex_three hAP hrelidx hx.1 hxA
  have hle : A ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (L : Set X) :=
    sup_le hAL (Subgroup.zpowers_le.mpr hx.2)
  exact hPL (hmax ▸ hle)

private lemma exists_t_of_not_le_normalizer {P A L : Subgroup X}
    (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1))
    (h3' : CFSG.pPrimeCore 3 X = ⊥) (hL : CFSG.IsComponent L)
    (hPL : ¬ P ≤ Subgroup.normalizer (L : Set X)) :
    ∃ t : X, t ∈ P ∧ t ∉ Subgroup.normalizer (L : Set X) ∧ t ∉ A ∧ t ^ 2 ∉ A := by
  classical
  obtain ⟨hAP, hAn, hrelidx, hcardP⟩ := le_and_relIndex_of_hyp327 hX hPZ
  have hAL : A ≤ Subgroup.normalizer (L : Set X) :=
    le_normalizer_of_isComponent hX.sylow h3' hX.elem hAP hAn hL
  have hAN : (A.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mpr hAn
  obtain ⟨t, htP, htN⟩ := Set.not_subset.mp hPL
  have htA : t ∉ A := fun h => htN (hAL h)
  have hqcard : Nat.card (↥P ⧸ A.subgroupOf P) = 3 := by
    rw [← Subgroup.index_eq_card]
    have hcard : Nat.card ↥(A.subgroupOf P) = 27 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hX.card]
    have h := Subgroup.card_mul_index (A.subgroupOf P)
    rw [hcard, hcardP] at h
    omega
  have ht2A : t ^ 2 ∉ A := by
    haveI := hAN
    intro h2A
    have hq2 : (QuotientGroup.mk (⟨t, htP⟩ : ↥P) : ↥P ⧸ A.subgroupOf P) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using h2A
    have hdvd : orderOf (QuotientGroup.mk (⟨t, htP⟩ : ↥P) : ↥P ⧸ A.subgroupOf P) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr hq2
    have hdvd3 : orderOf (QuotientGroup.mk (⟨t, htP⟩ : ↥P) : ↥P ⧸ A.subgroupOf P) ∣ 3 := by
      rw [← hqcard]
      exact orderOf_dvd_natCard _
    have hone : orderOf (QuotientGroup.mk (⟨t, htP⟩ : ↥P) : ↥P ⧸ A.subgroupOf P) = 1 := by
      have h := Nat.dvd_gcd hdvd hdvd3
      have h1 : Nat.gcd 2 3 = 1 := by norm_num
      rw [h1] at h
      exact Nat.dvd_one.mp h
    rw [orderOf_eq_one_iff] at hone
    exact htA (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hone))
  exact ⟨t, htP, htN, htA, ht2A⟩

private lemma inf_component_le_of_not_le_normalizer {P A L : Subgroup X}
    (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1))
    (h3' : CFSG.pPrimeCore 3 X = ⊥) (hL : CFSG.IsComponent L)
    (hPL : ¬ P ≤ Subgroup.normalizer (L : Set X)) :
    P ⊓ L ≤ A := by
  classical
  obtain ⟨hAP, hAn, hrelidx, -⟩ := le_and_relIndex_of_hyp327 hX hPZ
  have hAL : A ≤ Subgroup.normalizer (L : Set X) :=
    le_normalizer_of_isComponent hX.sylow h3' hX.elem hAP hAn hL
  intro x hx
  by_contra hxA
  have hmax := sup_zpowers_eq_of_relIndex_three hAP hrelidx hx.1 hxA
  have hle : A ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (L : Set X) :=
    sup_le hAL (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hx.2))
  exact hPL (hmax ▸ hle)

private lemma inf_map_conj_le_of_inf_le {P A : Subgroup X} {M : Subgroup X} {t : X}
    (hAP : A ≤ P) (hAn : P ≤ Subgroup.normalizer (A : Set X)) (htP : t ∈ P)
    (hM : P ⊓ M ≤ A) :
    P ⊓ M.map (MulAut.conj t⁻¹).toMonoidHom ≤ A := by
  intro y hy
  have hyP : y ∈ P := hy.1
  obtain ⟨z, hzM, rfl⟩ := Subgroup.mem_map.mp hy.2
  have hzP : z ∈ P := by
    have hconj : z = (MulAut.conj t) ((MulAut.conj t⁻¹) z) := by
      simp [MulAut.conj_apply]; group
    rw [hconj]
    exact mulAut_conj_mem_of_le_normalizer (Subgroup.le_normalizer (H := P)) htP hyP
  exact mulAut_conj_mem_of_le_normalizer hAn (P.inv_mem htP)
    (hM (Subgroup.mem_inf.mpr ⟨hzP, hzM⟩))

private lemma components_three_ne {P A L : Subgroup X} {t : X}
    (hPeq : P ⊓ Subgroup.normalizer (L : Set X) = A)
    (htP : t ∈ P) (ht2P : t ^ 2 ∈ P) (htA : t ∉ A) (ht2A : t ^ 2 ∉ A) :
    L.map (MulAut.conj t⁻¹).toMonoidHom ≠ L ∧
      (L.map (MulAut.conj t⁻¹).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom ≠ L ∧
      L.map (MulAut.conj t⁻¹).toMonoidHom ≠
        (L.map (MulAut.conj t⁻¹).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom := by
  have hne1 : L.map (MulAut.conj t⁻¹).toMonoidHom ≠ L := by
    intro h
    have hm : L.map (MulAut.conj t⁻¹).toMonoidHom = L := h
    have hcs : Subgroup.map (MulAut.conj t).toMonoidHom L = L := by
      calc Subgroup.map (MulAut.conj t).toMonoidHom L
          = Subgroup.map (MulAut.conj t).toMonoidHom
              (Subgroup.map (MulAut.conj t⁻¹).toMonoidHom L) := by rw [hm]
        _ = L := map_conj_map_conj_inv L t
    have htNL : t ∈ Subgroup.normalizer (L : Set X) :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hcs
    exact htA (hPeq ▸ Subgroup.mem_inf.mpr ⟨htP, htNL⟩)
  have hne2 : (L.map (MulAut.conj t⁻¹).toMonoidHom).map
      (MulAut.conj t⁻¹).toMonoidHom ≠ L := by
    intro h
    have hm : (L.map (MulAut.conj t⁻¹).toMonoidHom).map
        (MulAut.conj t⁻¹).toMonoidHom = L := h
    have hmap : Subgroup.map (MulAut.conj (t⁻¹ * t⁻¹)).toMonoidHom L = L := by
      rw [← Subgroup.map_conj_map_conj L t⁻¹ t⁻¹]
      exact hm
    have ht2N : t ^ 2 ∈ Subgroup.normalizer (L : Set X) := by
      have h2 : (t ^ 2)⁻¹ ∈ Subgroup.normalizer (L : Set X) := by
        have h2' : t⁻¹ * t⁻¹ ∈ Subgroup.normalizer (L : Set X) :=
          (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hmap
        simpa [pow_two] using h2'
      have := (Subgroup.normalizer (L : Set X)).inv_mem h2
      simpa using this
    exact ht2A (hPeq ▸ Subgroup.mem_inf.mpr ⟨ht2P, ht2N⟩)
  have hne3 : L.map (MulAut.conj t⁻¹).toMonoidHom ≠
      (L.map (MulAut.conj t⁻¹).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom := by
    intro h
    have h1 : Subgroup.map (MulAut.conj t).toMonoidHom
        (L.map (MulAut.conj t⁻¹).toMonoidHom) = L := map_conj_map_conj_inv L t
    have h2 : Subgroup.map (MulAut.conj t).toMonoidHom
        ((L.map (MulAut.conj t⁻¹).toMonoidHom).map
          (MulAut.conj t⁻¹).toMonoidHom) = L.map (MulAut.conj t⁻¹).toMonoidHom :=
      map_conj_map_conj_inv (L.map (MulAut.conj t⁻¹).toMonoidHom) t
    rw [h] at h1
    exact hne1 (h2.symm.trans h1)
  exact ⟨hne1, hne2, hne3⟩

private lemma exists_x2_data {P A L L1 : Subgroup X} {t : X}
    (hX : UC22.InS3.UC327.Hyp327 X P A)
    (h3' : CFSG.pPrimeCore 3 X = ⊥) (hL : CFSG.IsComponent L) (htP : t ∈ P)
    (hL1def : L1 = L.map (MulAut.conj t⁻¹).toMonoidHom)
    (hAn : P ≤ Subgroup.normalizer (A : Set X)) (hPLA : P ⊓ L ≤ A) :
    ∃ x1 x2 : X,
      x1 ∈ P ⊓ L ∧ x1 ∉ Subgroup.centralizer (L : Set X) ∧ x1 ∈ A ∧ x1 ≠ 1 ∧
      x2 ∈ L1 ∧ x2 ∈ P ∧ x2 ∈ A ∧ x2 ≠ 1 ∧
      x2 ∉ Subgroup.centralizer (L1 : Set X) := by
  classical
  obtain ⟨x1, hx1PL, hx1C⟩ :=
    exists_mem_inf_not_mem_centralizer_of_isComponent hX.sylow h3' hL
  have hx1P : x1 ∈ P := hx1PL.1
  have hx1L : x1 ∈ L := hx1PL.2
  have hx1A : x1 ∈ A := hPLA hx1PL
  have hx1ne : x1 ≠ 1 := fun h => hx1C (h ▸ Subgroup.one_mem _)
  let x2 : X := (MulAut.conj t⁻¹) x1
  have hx2L1 : x2 ∈ L1 := by
    rw [hL1def]; exact Subgroup.mem_map_of_mem _ hx1L
  have hx2P : x2 ∈ P := by
    show (MulAut.conj t⁻¹) x1 ∈ P
    exact mulAut_conj_mem_of_le_normalizer (Subgroup.le_normalizer (H := P)) (P.inv_mem htP) hx1P
  have hx2A : x2 ∈ A := by
    show (MulAut.conj t⁻¹) x1 ∈ A
    exact mulAut_conj_mem_of_le_normalizer hAn (P.inv_mem htP) hx1A
  have hx2ne : x2 ≠ 1 := by
    intro h
    apply hx1ne
    have := congrArg (MulAut.conj t) h
    simpa [x2, MulAut.conj_apply, mul_assoc] using this
  have hx2C : x2 ∉ Subgroup.centralizer (L1 : Set X) := by
    intro h
    apply hx1C
    have hh : (MulAut.conj t⁻¹).symm x2 ∈ Subgroup.centralizer (L : Set X) :=
      (mem_centralizer_map_mulEquiv_iff (L := L) (MulAut.conj t⁻¹) x2).mp
        (by simpa [hL1def] using h)
    have hx1eq : (MulAut.conj t⁻¹).symm x2 = x1 := by
      simpa [x2] using (MulEquiv.symm_apply_apply (MulAut.conj t⁻¹) x1)
    rwa [hx1eq] at hh
  exact ⟨x1, x2, hx1PL, hx1C, hx1A, hx1ne, hx2L1, hx2P, hx2A, hx2ne, hx2C⟩

private lemma exists_x3_data {P A L1 L2 : Subgroup X} {t x2 : X}
    (hAn : P ≤ Subgroup.normalizer (A : Set X)) (htP : t ∈ P)
    (hL2def : L2 = L1.map (MulAut.conj t⁻¹).toMonoidHom)
    (hx2L1 : x2 ∈ L1) (hx2P : x2 ∈ P) (hx2A : x2 ∈ A) (hx2ne : x2 ≠ 1)
    (hx2C : x2 ∉ Subgroup.centralizer (L1 : Set X)) :
    ∃ x3 : X, x3 ∈ L2 ∧ x3 ∈ P ∧ x3 ∈ A ∧ x3 ≠ 1 ∧
      x3 ∉ Subgroup.centralizer (L2 : Set X) := by
  let x3 : X := (MulAut.conj t⁻¹) x2
  have hx3L2 : x3 ∈ L2 := by
    rw [hL2def]; exact Subgroup.mem_map_of_mem _ hx2L1
  have hx3P : x3 ∈ P := by
    show (MulAut.conj t⁻¹) x2 ∈ P
    exact mulAut_conj_mem_of_le_normalizer (Subgroup.le_normalizer (H := P)) (P.inv_mem htP) hx2P
  have hx3A : x3 ∈ A := by
    show (MulAut.conj t⁻¹) x2 ∈ A
    exact mulAut_conj_mem_of_le_normalizer hAn (P.inv_mem htP) hx2A
  have hx3ne : x3 ≠ 1 := by
    intro h
    apply hx2ne
    have := congrArg (MulAut.conj t) h
    simpa [x3, MulAut.conj_apply, mul_assoc] using this
  have hx3C : x3 ∉ Subgroup.centralizer (L2 : Set X) := by
    intro h
    apply hx2C
    have hh : (MulAut.conj t⁻¹).symm x3 ∈ Subgroup.centralizer (L1 : Set X) :=
      (mem_centralizer_map_mulEquiv_iff (L := L1) (MulAut.conj t⁻¹) x3).mp
        (by simpa [hL2def] using h)
    have hx2eq : (MulAut.conj t⁻¹).symm x3 = x2 := by
      simpa [x3] using (MulEquiv.symm_apply_apply (MulAut.conj t⁻¹) x2)
    rwa [hx2eq] at hh
  exact ⟨x3, hx3L2, hx3P, hx3A, hx3ne, hx3C⟩

private lemma exists_xi_data {P A L L1 L2 : Subgroup X} {t : X}
    (hX : UC22.InS3.UC327.Hyp327 X P A)
    (h3' : CFSG.pPrimeCore 3 X = ⊥) (hL : CFSG.IsComponent L) (htP : t ∈ P)
    (hL1def : L1 = L.map (MulAut.conj t⁻¹).toMonoidHom)
    (hL2def : L2 = L1.map (MulAut.conj t⁻¹).toMonoidHom)
    (hAn : P ≤ Subgroup.normalizer (A : Set X)) (hPLA : P ⊓ L ≤ A) :
    ∃ x1 x2 x3 : X,
      x1 ∈ P ⊓ L ∧ x1 ∉ Subgroup.centralizer (L : Set X) ∧ x1 ∈ A ∧ x1 ≠ 1 ∧
      x2 ∈ L1 ∧ x2 ∈ P ∧ x2 ∈ A ∧ x2 ≠ 1 ∧
      x2 ∉ Subgroup.centralizer (L1 : Set X) ∧
      x3 ∈ L2 ∧ x3 ∈ P ∧ x3 ∈ A ∧ x3 ≠ 1 ∧
      x3 ∉ Subgroup.centralizer (L2 : Set X) := by
  obtain ⟨x1, x2, hx1PL, hx1C, hx1A, hx1ne, hx2L1, hx2P, hx2A, hx2ne, hx2C⟩ :=
    exists_x2_data hX h3' hL htP hL1def hAn hPLA
  obtain ⟨x3, hx3L2, hx3P, hx3A, hx3ne, hx3C⟩ :=
    exists_x3_data hAn htP hL2def hx2L1 hx2P hx2A hx2ne hx2C
  exact ⟨x1, x2, x3, hx1PL, hx1C, hx1A, hx1ne, hx2L1, hx2P, hx2A, hx2ne, hx2C,
    hx3L2, hx3P, hx3A, hx3ne, hx3C⟩

private lemma false_of_isCyclic_inf_centralizer_self {P A L L1 L2 : Subgroup X}
    {x2 x3 : X}
    (helem : CFSG.Open.IsElemAbelian 3 A)
    (hL : CFSG.IsComponent L) (hL1 : CFSG.IsComponent L1)
    (hL2 : CFSG.IsComponent L2) (hL1ne : L1 ≠ L) (hL2ne : L2 ≠ L) (hL12 : L1 ≠ L2)
    (hx2L1 : x2 ∈ L1) (hx2A : x2 ∈ A) (hx2ne : x2 ≠ 1)
    (hx3L2 : x3 ∈ L2) (hx3A : x3 ∈ A) (hx3ne : x3 ≠ 1)
    (hx3C : x3 ∉ Subgroup.centralizer (L2 : Set X))
    (hcyc : IsCyclic ↥(A ⊓ Subgroup.centralizer (L : Set X))) : False := by
  have hx2CL : x2 ∈ Subgroup.centralizer (L : Set X) :=
    le_centralizer_of_isComponent_of_ne hL1 hL hL1ne hx2L1
  have hx3CL : x3 ∈ Subgroup.centralizer (L : Set X) :=
    le_centralizer_of_isComponent_of_ne hL2 hL hL2ne hx3L2
  have hx3zp : x3 ∈ Subgroup.zpowers x2 :=
    mem_zpowers_of_pow_three_of_isCyclic
      (fun z hz => helem.2 z (Subgroup.mem_inf.mp hz).1) hcyc
      (Subgroup.mem_inf.mpr ⟨hx2A, hx2CL⟩) hx2ne
      (Subgroup.mem_inf.mpr ⟨hx3A, hx3CL⟩) hx3ne
  have hx3L1 : x3 ∈ L1 := Subgroup.zpowers_le.mpr hx2L1 hx3zp
  exact hx3C (le_centralizer_of_isComponent_of_ne hL1 hL2 hL12 hx3L1)

private lemma false_of_isCyclic_inf_centralizer_of_le_normalizer
    {P A L K L1 L2 : Subgroup X} {t x1 x2 : X}
    (helem : CFSG.Open.IsElemAbelian 3 A)
    (hPL : ¬ P ≤ Subgroup.normalizer (L : Set X))
    (hcase : P ≤ Subgroup.normalizer (K : Set X))
    (hL : CFSG.IsComponent L) (hK : CFSG.IsComponent K)
    (hL1 : CFSG.IsComponent L1) (htP : t ∈ P)
    (hL1def : L1 = L.map (MulAut.conj t⁻¹).toMonoidHom)
    (hL2def : L2 = L1.map (MulAut.conj t⁻¹).toMonoidHom)
    (hL1ne : L1 ≠ L) (hL12 : L1 ≠ L2)
    (hx1L : x1 ∈ L) (hx1A : x1 ∈ A) (hx1ne : x1 ≠ 1)
    (hx2L1 : x2 ∈ L1) (hx2A : x2 ∈ A) (hx2ne : x2 ≠ 1)
    (hx2C : x2 ∉ Subgroup.centralizer (L1 : Set X))
    (hcyc : IsCyclic ↥(A ⊓ Subgroup.centralizer (K : Set X))) : False := by
  have hKneL : K ≠ L := fun h => hPL (h ▸ hcase)
  have hKneL1 : K ≠ L1 := by
    intro h
    have htNL1 : t ∈ Subgroup.normalizer (L1 : Set X) := h ▸ hcase htP
    have hmap : Subgroup.map (MulAut.conj t).toMonoidHom L1 = L1 :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp htNL1
    have hmapL : Subgroup.map (MulAut.conj t).toMonoidHom L1 = L := by
      rw [hL1def]
      exact map_conj_map_conj_inv L t
    exact hL1ne (hmapL.symm.trans hmap).symm
  have hKneL2 : K ≠ L2 := by
    intro h
    have htNL2 : t ∈ Subgroup.normalizer (L2 : Set X) := h ▸ hcase htP
    have hmap : Subgroup.map (MulAut.conj t).toMonoidHom L2 = L2 :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp htNL2
    have hmapL : Subgroup.map (MulAut.conj t).toMonoidHom L2 = L1 := by
      rw [hL2def, hL1def]
      exact map_conj_map_conj_inv _ t
    exact hL12 (hmapL.symm.trans hmap)
  have hx1CK : x1 ∈ Subgroup.centralizer (K : Set X) :=
    le_centralizer_of_isComponent_of_ne hL hK hKneL.symm hx1L
  have hx2CK : x2 ∈ Subgroup.centralizer (K : Set X) :=
    le_centralizer_of_isComponent_of_ne hL1 hK hKneL1.symm hx2L1
  have hx2zp : x2 ∈ Subgroup.zpowers x1 :=
    mem_zpowers_of_pow_three_of_isCyclic
      (fun z hz => helem.2 z (Subgroup.mem_inf.mp hz).1) hcyc
      (Subgroup.mem_inf.mpr ⟨hx1A, hx1CK⟩) hx1ne
      (Subgroup.mem_inf.mpr ⟨hx2A, hx2CK⟩) hx2ne
  have hx2L : x2 ∈ L := Subgroup.zpowers_le.mpr hx1L hx2zp
  exact hx2C (le_centralizer_of_isComponent_of_ne hL hL1 hL1ne.symm hx2L)

theorem not_isCyclic_inf_centralizer_of_not_le_normalizer {P A L K : Subgroup X}
    (hX : UC22.InS3.UC327.Hyp327 X P A) (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1))
    (h3' : CFSG.pPrimeCore 3 X = ⊥) (hL : CFSG.IsComponent L)
    (hPL : ¬ P ≤ Subgroup.normalizer (L : Set X)) (hK : CFSG.IsComponent K)
    (hKL : K = L ∨ P ≤ Subgroup.normalizer (K : Set X)) :
    ¬ IsCyclic ↥(A ⊓ Subgroup.centralizer (K : Set X)) := by
  classical
  intro hcyc
  obtain ⟨hAP, hAn, -, -⟩ := le_and_relIndex_of_hyp327 hX hPZ
  have hPeq := inf_normalizer_eq_of_not_le_normalizer hX hPZ h3' hL hPL
  obtain ⟨t, htP, -, htA, ht2A⟩ := exists_t_of_not_le_normalizer hX hPZ h3' hL hPL
  have ht2P : t ^ 2 ∈ P := P.pow_mem htP 2
  have hPLA : P ⊓ L ≤ A := inf_component_le_of_not_le_normalizer hX hPZ h3' hL hPL
  let L1 : Subgroup X := L.map (MulAut.conj t⁻¹).toMonoidHom
  let L2 : Subgroup X := L1.map (MulAut.conj t⁻¹).toMonoidHom
  have hL1def : L1 = L.map (MulAut.conj t⁻¹).toMonoidHom := rfl
  have hL2def : L2 = L1.map (MulAut.conj t⁻¹).toMonoidHom := rfl
  have hL1 : CFSG.IsComponent L1 := by
    rw [hL1def]; exact CFSG.LocalCores.isComponent_map_mulEquiv _ hL
  have hL2 : CFSG.IsComponent L2 := by
    rw [hL2def]; exact CFSG.LocalCores.isComponent_map_mulEquiv _ hL1
  obtain ⟨hL1ne, hL2ne, hL12⟩ := components_three_ne hPeq htP ht2P htA ht2A
  have hPL1A : P ⊓ L1 ≤ A := by
    rw [hL1def]
    exact inf_map_conj_le_of_inf_le hAP hAn htP hPLA
  have hPL2A : P ⊓ L2 ≤ A := by
    rw [hL2def]
    exact inf_map_conj_le_of_inf_le hAP hAn htP hPL1A
  obtain ⟨x1, x2, x3, hx1PL, -, hx1A, hx1ne, hx2L1, -, hx2A, hx2ne, hx2C,
    hx3L2, -, hx3A, hx3ne, hx3C⟩ :=
    exists_xi_data hX h3' hL htP hL1def hL2def hAn hPLA
  rcases hKL with hcase | hcase
  · rw [hcase] at hcyc
    exact false_of_isCyclic_inf_centralizer_self (P := P) hX.elem hL hL1 hL2 hL1ne hL2ne hL12
      hx2L1 hx2A hx2ne hx3L2 hx3A hx3ne hx3C hcyc
  · exact false_of_isCyclic_inf_centralizer_of_le_normalizer (P := P) hX.elem hPL hcase hL hK
      hL1 htP hL1def hL2def hL1ne hL12 hx1PL.2 hx1A hx1ne hx2L1 hx2A hx2ne hx2C hcyc

private lemma le_normalizer_of_isCyclic_inf_centralizer {P A L : Subgroup X}
    (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1))
    (h3' : CFSG.pPrimeCore 3 X = ⊥) (hL : CFSG.IsComponent L)
    (hcyc : IsCyclic ↥(A ⊓ Subgroup.centralizer (L : Set X))) :
    P ≤ Subgroup.normalizer (L : Set X) := by
  by_contra h
  exact (not_isCyclic_inf_centralizer_of_not_le_normalizer hX hPZ h3' hL h hL (Or.inl rfl))
    hcyc

private lemma eq_of_isComponent_of_isCyclic_inf_centralizer {P A L : Subgroup X}
    (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1))
    (h3' : CFSG.pPrimeCore 3 X = ⊥) (hL : CFSG.IsComponent L)
    (hcyc : IsCyclic ↥(A ⊓ Subgroup.centralizer (L : Set X)))
    (hPN : P ≤ Subgroup.normalizer (L : Set X)) {K : Subgroup X}
    (hK : CFSG.IsComponent K) : K = L := by
  by_contra hne
  by_cases hPK : P ≤ Subgroup.normalizer (K : Set X)
  · have hPLn : P ≤ Subgroup.normalizer ((P ⊓ L : Subgroup X) : Set X) := by
      refine (le_inf Subgroup.le_normalizer hPN).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hPKn : P ≤ Subgroup.normalizer ((P ⊓ K : Subgroup X) : Set X) := by
      refine (le_inf Subgroup.le_normalizer hPK).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hcentKL : K ≤ Subgroup.centralizer (L : Set X) :=
      le_centralizer_of_isComponent_of_ne hK hL hne
    have hcentLK : L ≤ Subgroup.centralizer (K : Set X) :=
      le_centralizer_of_isComponent_of_ne hL hK (Ne.symm hne)
    have hcomm : (P ⊓ L : Subgroup X) ≤
        Subgroup.centralizer ((P ⊓ K : Subgroup X) : Set X) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_iff.mp (hcentLK hx.2) y hy.2
    rcases le_or_le_of_le_centralizer_of_zwr hPZ inf_le_left inf_le_left hPLn hPKn hcomm
      with hle | hle
    · obtain ⟨x, hx, hxC⟩ :=
        exists_mem_inf_not_mem_centralizer_of_isComponent hX.sylow h3' hL
      exact hxC (hcentKL (hle hx).2)
    · obtain ⟨x, hx, hxC⟩ :=
        exists_mem_inf_not_mem_centralizer_of_isComponent hX.sylow h3' hK
      exact hxC (hcentLK (hle hx).2)
  · exact (not_isCyclic_inf_centralizer_of_not_le_normalizer hX hPZ h3' hK hPK hL
      (Or.inr hPN)) hcyc

theorem layer_eq_and_inf_centralizer_le_of_isCyclic {P A L : Subgroup X}
    (hX : UC22.InS3.UC327.Hyp327 X P A) (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1))
    (h3' : CFSG.pPrimeCore 3 X = ⊥) (hL : CFSG.IsComponent L)
    (hcyc : IsCyclic ↥(A ⊓ Subgroup.centralizer (L : Set X))) :
    CFSG.layer X = L ∧
      P ⊓ Subgroup.centralizer (L : Set X) ≤ Subgroup.centralizer (P : Set X) := by
  classical
  have hAP : A ≤ P := by
    rw [hX.jA]
    exact Subgroup.map_subtype_le _
  have hPN := le_normalizer_of_isCyclic_inf_centralizer hX hPZ h3' hL hcyc
  have honly : ∀ K : Subgroup X, CFSG.IsComponent K → K = L := fun K hK =>
    eq_of_isComponent_of_isCyclic_inf_centralizer hX hPZ h3' hL hcyc hPN hK
  have hlayer : CFSG.layer X = L := by
    rw [CFSG.layer.eq_sSup]
    exact le_antisymm (sSup_le fun K hK => by rw [honly K hK]) (le_sSup hL)
  refine ⟨hlayer, ?_⟩
  have hAn : P ≤ Subgroup.normalizer (A : Set X) := by
    rw [hX.jA]
    exact CFSG.Quasithin.BlueprintB2.le_normalizer_map_elemThompson (p := 3) P
  have hnN : P ≤ Subgroup.normalizer
      ((P ⊓ Subgroup.centralizer (L : Set X) : Subgroup X) : Set X) := by
    refine (le_inf Subgroup.le_normalizer ?_).trans
      Subgroup.inf_normalizer_le_normalizer_inf
    exact hPN.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer L)
  have hNA : (P ⊓ Subgroup.centralizer (L : Set X)) ⊓ A =
      A ⊓ Subgroup.centralizer (L : Set X) := by
    rw [inf_assoc, inf_comm (Subgroup.centralizer (L : Set X)) A, ← inf_assoc,
      inf_eq_right.mpr hAP]
  refine le_centralizer_of_isCyclic_inf_of_zwr hPZ hX.elem hX.card hAP inf_le_left hnN ?_
  rw [hNA]
  exact hcyc

end A10Gen

theorem kFactE27SignalizerComp_of_one (h : KFactE27SignalizerOne) :
    KFactE27SignalizerComp := by
  intro X _ _ P A hK hX hP h3' hbal L hL hcyc W hW hcop
  obtain ⟨hlayer, hinf⟩ :=
    A10Gen.layer_eq_and_inf_centralizer_le_of_isCyclic hX hP h3' hL hcyc
  exact h X P A hK hX hP h3' hbal L hL hlayer hinf W hW hcop

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
