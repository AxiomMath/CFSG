module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_pCoreOf_le_M (D : Data G) {z : G}
    (hS : IsSylowIn 2 (D.T ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G))) :
    pCoreOf 2 (centralizer ({z} : Set G)) ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.Quasithin.pCoreOf_le_of_isSylowIn hS).trans (inf_le_left.trans D.sylowM.le)

private lemma s16c1_conj_mem_pCoreOf {K : Subgroup G} {k : G} (hk : k ∈ K) :
    ∀ o ∈ pCoreOf 2 K, k * o * k⁻¹ ∈ pCoreOf 2 K := by
  intro o ho
  simp only [pCoreOf, Subgroup.mem_map] at ho ⊢
  obtain ⟨n, hn, rfl⟩ := ho
  exact ⟨⟨k, hk⟩ * n * ⟨k, hk⟩⁻¹,
    (CFSG.pCore_normal (p := 2) (G := ↥K)).conj_mem n hn ⟨k, hk⟩, by simp⟩

theorem s16c1_conjSubgroup_pCoreOf_self (K : Subgroup G) {k : G} (hk : k ∈ K) :
    conjSubgroup (pCoreOf 2 K) k = pCoreOf 2 K := by
  ext x
  rw [mem_conjSubgroup_iff]
  constructor
  · intro hx
    have hx' := s16c1_conj_mem_pCoreOf (K := K) (K.inv_mem hk) (k * x * k⁻¹) hx
    rwa [show k⁻¹ * (k * x * k⁻¹) * (k⁻¹)⁻¹ = x by group] at hx'
  · intro hx
    exact s16c1_conj_mem_pCoreOf (K := K) hk x hx

theorem s16c1_zpowers_le_pCoreOf {z : G} (hz : z ^ 2 = 1) :
    Subgroup.zpowers z ≤ pCoreOf 2 (centralizer ({z} : Set G)) := by
  let H := centralizer ({z} : Set G)
  have hzH : z ∈ H := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
  have hnormal : (Subgroup.zpowers (⟨z, hzH⟩ : ↥H)).Normal := by
    apply Subgroup.normal_of_le_center
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.mp g.2) z (by simp)).symm
  have hpg : IsPGroup 2 (Subgroup.zpowers (⟨z, hzH⟩ : ↥H)) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers]
    simpa using (orderOf_dvd_iff_pow_eq_one.mpr (show (⟨z, hzH⟩ : ↥H) ^ 2 = 1 by
      apply Subtype.ext
      simpa using hz))
  rw [Subgroup.zpowers_le]
  change z ∈ (CFSG.pCore 2 ↥H).map H.subtype
  exact ⟨⟨z, hzH⟩, le_sSup (s := {K : Subgroup ↥H | K.Normal ∧ IsPGroup 2 K})
    ⟨hnormal, hpg⟩ (Subgroup.mem_zpowers _), rfl⟩

theorem s16c1_uOne_le_eOne (V : Subgroup G) (z : G) : uOne V z ≤ eOne V z := by
  rw [eOne, hConjClosure]
  exact le_iSup_of_le ⟨1, one_mem _⟩ (le_of_eq (conjSubgroup_one (uOne V z)).symm)

theorem s16c1_eOne_le_pCoreOf (V : Subgroup G) (z : G) :
    eOne V z ≤ pCoreOf 2 (centralizer ({z} : Set G)) := by
  rw [eOne, hConjClosure]
  apply iSup_le
  intro h
  calc conjSubgroup (uOne V z) (h : G)
      ≤ conjSubgroup (pCoreOf 2 (centralizer ({z} : Set G))) (h : G) :=
        Subgroup.map_mono inf_le_right
    _ = pCoreOf 2 (centralizer ({z} : Set G)) :=
        s16c1_conjSubgroup_pCoreOf_self (centralizer ({z} : Set G)) h.2

theorem s16c1_pCoreOf_le_normalizer_uOne {V : Subgroup G} {z : G}
    (hP : pCoreOf 2 (centralizer ({z} : Set G)) ≤ normalizer (V : Set G)) :
    pCoreOf 2 (centralizer ({z} : Set G)) ≤ normalizer ((uOne V z : Subgroup G) : Set G) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [uOne, Subgroup.mem_inf]
  constructor
  · intro hx
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hP hp) x).mp hx.1,
      s16c1_conj_mem_pCoreOf (K := centralizer ({z} : Set G))
        ((Subgroup.map_subtype_le (CFSG.pCore 2 ↥(centralizer ({z} : Set G)))) hp) x hx.2⟩
  · intro hx
    have hp' : p⁻¹ ∈ pCoreOf 2 (centralizer ({z} : Set G)) :=
      (pCoreOf 2 (centralizer ({z} : Set G))).inv_mem hp
    refine ⟨?_, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.mp (hP hp') (p * x * p⁻¹)).mp hx.1
      rwa [show p⁻¹ * (p * x * p⁻¹) * p⁻¹⁻¹ = x by group] at h
    · have h := s16c1_conj_mem_pCoreOf (K := centralizer ({z} : Set G))
        ((Subgroup.map_subtype_le (CFSG.pCore 2 ↥(centralizer ({z} : Set G)))) hp')
        (p * x * p⁻¹) hx.2
      rwa [show p⁻¹ * (p * x * p⁻¹) * (p⁻¹)⁻¹ = x by group] at h

theorem s16c1_uOne_subgroupOf_normal {V : Subgroup G} {z : G}
    (hP : pCoreOf 2 (centralizer ({z} : Set G)) ≤ normalizer (V : Set G)) :
    ((uOne V z).subgroupOf (eOne V z)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (s16c1_uOne_le_eOne V z)]
  exact (s16c1_eOne_le_pCoreOf V z).trans (s16c1_pCoreOf_le_normalizer_uOne hP)

private theorem s16c1_conjSubgroup_inf (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊓ B) g = conjSubgroup A g ⊓ conjSubgroup B g := by
  ext x
  simp only [mem_conjSubgroup_iff, Subgroup.mem_inf]

theorem s16c1_conjSubgroup_uOne_eq {V : Subgroup G} {z h : G}
    (hh : h ∈ centralizer ({z} : Set G)) (hV : h ∈ normalizer (V : Set G)) :
    conjSubgroup (uOne V z) h = uOne V z := by
  rw [uOne, s16c1_conjSubgroup_inf,
    (conjSubgroup_eq_iff_mem_normalizer (A := V) (g := h)).2 hV,
    s16c1_conjSubgroup_pCoreOf_self (centralizer ({z} : Set G)) hh]

theorem s16c1_comm_uOne_conj_le {V : Subgroup G} {z h : G}
    (hh : h ∈ centralizer ({z} : Set G))
    (hP : pCoreOf 2 (centralizer ({z} : Set G)) ≤ normalizer (V : Set G)) :
    ⁅uOne V z, conjSubgroup (uOne V z) h⁆ ≤ uOne V z ⊓ conjSubgroup (uOne V z) h := by
  let H := centralizer ({z} : Set G)
  let U := uOne V z
  have hconj : conjSubgroup U h = conjSubgroup V h ⊓ pCoreOf 2 H := by
    rw [show U = V ⊓ pCoreOf 2 H from rfl, s16c1_conjSubgroup_inf,
      s16c1_conjSubgroup_pCoreOf_self H hh]
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hb' : b ∈ conjSubgroup V h ⊓ pCoreOf 2 H := hconj ▸ hb
  have hbP : b ∈ pCoreOf 2 H := hb'.2
  have haP : a ∈ pCoreOf 2 H := ha.2
  have hbaV : b * a⁻¹ * b⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hP hbP) a⁻¹).mp (V.inv_mem ha.1)
  have hbaP : b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 H :=
    s16c1_conj_mem_pCoreOf (K := H) (Subgroup.map_subtype_le (CFSG.pCore 2 ↥H) hbP)
      a⁻¹ ((pCoreOf 2 H).inv_mem haP)
  have hbaU : b * a⁻¹ * b⁻¹ ∈ U := Subgroup.mem_inf.mpr ⟨hbaV, hbaP⟩
  have haNH : a ∈ normalizer ((conjSubgroup V h : Subgroup G) : Set G) := by
    have hc : h * a * h⁻¹ ∈ normalizer (V : Set G) :=
      hP (s16c1_conj_mem_pCoreOf (K := H) hh a haP)
    have h1 : a ∈ conjSubgroup (normalizer (V : Set G)) h := by
      rw [mem_conjSubgroup_iff]
      simpa using hc
    have hmap : conjSubgroup (normalizer (V : Set G)) h =
        normalizer ((conjSubgroup V h : Subgroup G) : Set G) := by
      simpa only [conjSubgroup] using
        (Subgroup.map_equiv_normalizer_eq (V : Subgroup G) (MulAut.conj h⁻¹))
    rwa [← hmap]
  have haNP : a ∈ normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    (conjSubgroup_eq_iff_mem_normalizer (A := pCoreOf 2 H) (g := a)).mp
      (s16c1_conjSubgroup_pCoreOf_self H
        ((Subgroup.map_subtype_le (CFSG.pCore 2 ↥H)) haP))
  have haNW : a ∈ normalizer ((conjSubgroup U h : Subgroup G) : Set G) := by
    rw [hconj]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨haNH, haNP⟩
  have habW : a * b * a⁻¹ ∈ conjSubgroup U h :=
    (Subgroup.mem_normalizer_iff.mp haNW b).mp hb
  rw [commutatorElement_def, Subgroup.mem_inf]
  exact ⟨by simpa only [mul_assoc] using U.mul_mem ha hbaU,
    (conjSubgroup U h).mul_mem habW ((conjSubgroup U h).inv_mem hb)⟩

theorem s16c1_ti_of_core {M V : Subgroup G} {z : G} (hM : M ≤ normalizer (V : Set G))
    (hcore : ∀ h ∈ centralizer ({z} : Set G),
      ¬ uOne V z ⊓ conjSubgroup (uOne V z) h ≤ Subgroup.zpowers z → h ∈ M) :
    ∀ h ∈ centralizer ({z} : Set G),
      conjSubgroup (uOne V z) h = uOne V z ∨
        uOne V z ⊓ conjSubgroup (uOne V z) h ≤ Subgroup.zpowers z := by
  intro h hh
  by_cases hle : uOne V z ⊓ conjSubgroup (uOne V z) h ≤ Subgroup.zpowers z
  · exact Or.inr hle
  · exact Or.inl (s16c1_conjSubgroup_uOne_eq hh (hM (hcore h hh hle)))

theorem s16c1_closure_comm_sq {T : Set G} {X Z : Subgroup G} (hX : Subgroup.closure T = X)
    (hZ : ∀ c ∈ Z, ∀ x ∈ X, c * x = x * c) (hcomm : ∀ a ∈ T, ∀ b ∈ T, ⁅a, b⁆ ∈ Z)
    (hsq : ∀ a ∈ T, a ^ 2 ∈ Z) : ⁅X, X⁆ ≤ Z ∧ ∀ e ∈ X, e ^ 2 ∈ Z := by
  have key : ∀ a ∈ T, ∀ b ∈ X, ⁅a, b⁆ ∈ Z := by
    intro a ha b hb
    rw [← hX] at hb
    induction hb using Subgroup.closure_induction with
    | mem x hx => exact hcomm a ha x hx
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hxX : x ∈ X := hX ▸ hx
      have hyc : ⁅a, y⁆ * x = x * ⁅a, y⁆ := hZ _ ihy x hxX
      have e : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      have hxd : x * ⁅a, y⁆ * x⁻¹ = ⁅a, y⁆ := by rw [← hyc]; group
      rw [e, hxd]
      exact Z.mul_mem ihx ihy
    | inv x hx ihx =>
      have hxX : x ∈ X := hX ▸ hx
      have hcx : ⁅a, x⁆ * x = x * ⁅a, x⁆ := hZ _ ihx x hxX
      have hcx' : ⁅a, x⁆⁻¹ * x = x * ⁅a, x⁆⁻¹ :=
        (Commute.inv_left (show Commute ⁅a, x⁆ x from hcx)).eq
      have e : ⁅a, x⁻¹⁆ = x⁻¹ * ⁅a, x⁆⁻¹ * x := by
        simp only [commutatorElement_def]; group
      have : ⁅a, x⁻¹⁆ = ⁅a, x⁆⁻¹ := by
        rw [e, mul_assoc, hcx', ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact Z.inv_mem ihx
  have hgen : ∀ a ∈ X, ∀ b ∈ X, ⁅a, b⁆ ∈ Z := by
    intro a ha
    rw [← hX] at ha
    induction ha using Subgroup.closure_induction with
    | mem x hx => exact fun b hb => key x hx b hb
    | one => intro b _; simp
    | mul x y hx hy ihx ihy =>
      intro b hb
      have hxX : x ∈ X := hX ▸ hx
      have hyc : ⁅y, b⁆ * x = x * ⁅y, b⁆ := hZ _ (ihy b hb) x hxX
      have e : ⁅x * y, b⁆ = x * ⁅y, b⁆ * x⁻¹ * ⁅x, b⁆ := by
        simp only [commutatorElement_def]; group
      have hxd : x * ⁅y, b⁆ * x⁻¹ = ⁅y, b⁆ := by rw [← hyc]; group
      rw [e, hxd]
      exact Z.mul_mem (ihy b hb) (ihx b hb)
    | inv x hx ihx =>
      intro b hb
      have hxX : x ∈ X := hX ▸ hx
      have hcx : ⁅x, b⁆ * x = x * ⁅x, b⁆ := hZ _ (ihx b hb) x hxX
      have hcx' : ⁅x, b⁆⁻¹ * x = x * ⁅x, b⁆⁻¹ :=
        (Commute.inv_left (show Commute ⁅x, b⁆ x from hcx)).eq
      have e : ⁅x⁻¹, b⁆ = x⁻¹ * ⁅x, b⁆⁻¹ * x := by
        simp only [commutatorElement_def]; group
      have : ⁅x⁻¹, b⁆ = ⁅x, b⁆⁻¹ := by
        rw [e, mul_assoc, hcx', ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact Z.inv_mem (ihx b hb)
  refine ⟨Subgroup.commutator_le.mpr hgen, ?_⟩
  intro e he
  rw [← hX] at he
  induction he using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxX : x ∈ X := hX ▸ hx
    have hyX : y ∈ X := hX ▸ hy
    have hc : ⁅y, x⁆ ∈ Z := hgen y hyX x hxX
    have hcent : x * ⁅y, x⁆ = ⁅y, x⁆ * x := (hZ _ hc x hxX).symm
    have e : (x * y) ^ 2 = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by
      nth_rewrite 1 [pow_two]
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (⁅y, x⁆ * (x * y)) * y := by
              rw [show ⁅y, x⁆ * (x * y) = y * x by
                simp only [commutatorElement_def]; group]
        _ = (x * ⁅y, x⁆) * (x * (y * y)) := by group
        _ = (⁅y, x⁆ * x) * (x * (y * y)) := by rw [hcent]
        _ = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by
              rw [pow_two, pow_two]
              group
    rw [e]
    exact Z.mul_mem hc (Z.mul_mem ihx ihy)
  | inv x hx ihx =>
    have e : (x⁻¹) ^ 2 = (x ^ 2)⁻¹ := by group
    rw [e]
    exact Z.inv_mem ihx

private lemma s16c1_conjSubgroup_zpowers_eq {z h : G} (hh : h ∈ centralizer ({z} : Set G)) :
    conjSubgroup (Subgroup.zpowers z) h = Subgroup.zpowers z := by
  rw [conjSubgroup_eq_iff_mem_normalizer, Subgroup.mem_normalizer_iff]
  intro x
  have hzh : Commute z h := (Subgroup.mem_centralizer_iff.mp hh) z (by simp)
  constructor
  · intro hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    rw [← (hzh.zpow_left m).eq]
    group
  · intro hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    have hx_eq : x = h⁻¹ * z ^ m * h := by rw [hm]; group
    have hcalc : h⁻¹ * z ^ m * h = z ^ m := by
      calc h⁻¹ * z ^ m * h = h⁻¹ * (z ^ m * h) := by group
        _ = h⁻¹ * (h * z ^ m) := by rw [(hzh.zpow_left m).eq]
        _ = z ^ m := by group
    rw [hx_eq, hcalc]

theorem s16c1_phi_eOne {V : Subgroup G} {z : G} (hV : IsElemAbelian 2 V)
    (hP : pCoreOf 2 (centralizer ({z} : Set G)) ≤ normalizer (V : Set G))
    (hTI : ∀ h ∈ centralizer ({z} : Set G),
      conjSubgroup (uOne V z) h = uOne V z ∨
        uOne V z ⊓ conjSubgroup (uOne V z) h ≤ Subgroup.zpowers z) :
    ⁅eOne V z, eOne V z⁆ ≤ Subgroup.zpowers z ∧ ∀ e ∈ eOne V z, e ^ 2 ∈ Subgroup.zpowers z := by
  let H := centralizer ({z} : Set G)
  let U := uOne V z
  let T : Set G := ⋃ h : ↥H, (conjSubgroup U h : Set G)
  refine s16c1_closure_comm_sq (X := eOne V z) (Z := Subgroup.zpowers z) (T := T) ?_ ?_ ?_ ?_
  · show Subgroup.closure (⋃ h : ↥H, (conjSubgroup U h : Set G)) = eOne V z
    rw [eOne, hConjClosure]
    exact (Subgroup.iSup_eq_closure (fun h : ↥H => conjSubgroup U h)).symm
  · intro c hc x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hxP : x ∈ pCoreOf 2 H := s16c1_eOne_le_pCoreOf V z hx
    have hxH : x ∈ H := (Subgroup.map_subtype_le (CFSG.pCore 2 ↥H)) hxP
    have hzx : z * x = x * z := (Subgroup.mem_centralizer_iff.mp hxH) z (by simp)
    exact (Commute.zpow_left hzx k).eq
  · intro a ha b hb
    change a ∈ (⋃ h : ↥H, (conjSubgroup U h : Set G)) at ha
    change b ∈ (⋃ h : ↥H, (conjSubgroup U h : Set G)) at hb
    rw [Set.mem_iUnion] at ha hb
    obtain ⟨h, haU⟩ := ha
    obtain ⟨h', hbU⟩ := hb
    set k : G := (h : G) * (h' : G)⁻¹ with hk
    have hkH : k ∈ H := by
      rw [hk]
      exact H.mul_mem h.2 (H.inv_mem h'.2)
    have ha'' : (h' : G) * a * (h' : G)⁻¹ ∈ conjSubgroup U k := by
      rw [mem_conjSubgroup_iff]
      have hcalc : k * ((h' : G) * a * (h' : G)⁻¹) * k⁻¹
          = (h : G) * a * (h : G)⁻¹ := by
        rw [hk]; group
      rw [hcalc]
      exact mem_conjSubgroup_iff.mp haU
    have hb' : (h' : G) * b * (h' : G)⁻¹ ∈ U := mem_conjSubgroup_iff.mp hbU
    have hkey : ⁅(h' : G) * a * (h' : G)⁻¹, (h' : G) * b * (h' : G)⁻¹⁆ ∈
        Subgroup.zpowers z := by
      rcases hTI k hkH with hkU | hkTI
      · have hkU' : conjSubgroup U k = U := by
          rw [show U = uOne V z from rfl]
          exact hkU
        have ha''U : (h' : G) * a * (h' : G)⁻¹ ∈ U := hkU' ▸ ha''
        have hb'V : (h' : G) * b * (h' : G)⁻¹ ∈ V := hb'.1
        have ha''V : (h' : G) * a * (h' : G)⁻¹ ∈ V := ha''U.1
        letI : IsMulCommutative ↥V := hV.1
        have hcommute : Commute ((h' : G) * a * (h' : G)⁻¹)
            ((h' : G) * b * (h' : G)⁻¹) :=
          congrArg Subtype.val (mul_comm' (⟨_, ha''V⟩ : ↥V) (⟨_, hb'V⟩ : ↥V))
        rw [hcommute.commutator_eq]
        exact Subgroup.one_mem _
      · have hcomm' : ⁅(h' : G) * b * (h' : G)⁻¹, (h' : G) * a * (h' : G)⁻¹⁆ ∈
            U ⊓ conjSubgroup U k :=
          s16c1_comm_uOne_conj_le (V := V) (z := z) (h := k) hkH hP
            (Subgroup.commutator_mem_commutator hb' ha'')
        have hz' : ⁅(h' : G) * b * (h' : G)⁻¹, (h' : G) * a * (h' : G)⁻¹⁆ ∈
            Subgroup.zpowers z := hkTI hcomm'
        rw [← commutatorElement_inv]
        exact Subgroup.inv_mem _ hz'
    have hzconj : conjSubgroup (Subgroup.zpowers z) ((h' : G)⁻¹) = Subgroup.zpowers z :=
      s16c1_conjSubgroup_zpowers_eq (z := z) (h := (h' : G)⁻¹) (H.inv_mem h'.2)
    have hc : ⁅(h' : G) * a * (h' : G)⁻¹, (h' : G) * b * (h' : G)⁻¹⁆ ∈
        conjSubgroup (Subgroup.zpowers z) ((h' : G)⁻¹) := by
      rw [hzconj]; exact hkey
    have hfinal : (h' : G)⁻¹ *
        ⁅(h' : G) * a * (h' : G)⁻¹, (h' : G) * b * (h' : G)⁻¹⁆ * (h' : G) ∈
        Subgroup.zpowers z := by
      simpa using mem_conjSubgroup_iff.mp hc
    rwa [show (h' : G)⁻¹ *
        ⁅(h' : G) * a * (h' : G)⁻¹, (h' : G) * b * (h' : G)⁻¹⁆ * (h' : G) = ⁅a, b⁆ by
      simp only [commutatorElement_def]; group] at hfinal
  · intro a ha
    change a ∈ (⋃ h : ↥H, (conjSubgroup U h : Set G)) at ha
    rw [Set.mem_iUnion] at ha
    obtain ⟨h, hhU⟩ := ha
    have hhaU : (h : G) * a * (h : G)⁻¹ ∈ U := mem_conjSubgroup_iff.mp hhU
    have hhaV : (h : G) * a * (h : G)⁻¹ ∈ V := hhaU.1
    have hsq1 : ((h : G) * a * (h : G)⁻¹) ^ 2 = 1 := hV.2 _ hhaV
    have hconj : ((h : G) * a * (h : G)⁻¹) ^ 2 = (h : G) * a ^ 2 * (h : G)⁻¹ := by
      rw [show (h : G) * a * (h : G)⁻¹ = MulAut.conj (h : G) a by
        simp [MulAut.conj_apply]]
      rw [← map_pow (MulAut.conj (h : G)) a 2]
      simp [MulAut.conj_apply]
    have hcalc : a ^ 2 = (h : G)⁻¹ * ((h : G) * a * (h : G)⁻¹) ^ 2 * (h : G) := by
      rw [hconj]
      group
    rw [hcalc, hsq1]
    simp

theorem s16c1_comm_V_eOne_le {V : Subgroup G} {z : G} (hV : IsElemAbelian 2 V) (hz : z ∈ V)
    (hP : pCoreOf 2 (centralizer ({z} : Set G)) ≤ normalizer (V : Set G)) :
    ⁅V, eOne V z⁆ ≤ uOne V z := by
  let H := centralizer ({z} : Set G)
  let P := pCoreOf 2 H
  have hVH : V ≤ H := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    letI : IsMulCommutative ↥V := hV.1
    exact congrArg Subtype.val (mul_comm' (⟨z, hz⟩ : ↥V) (⟨v, hv⟩ : ↥V))
  rw [Subgroup.commutator_le]
  intro v hv e he
  have heP : e ∈ P := s16c1_eOne_le_pCoreOf V z he
  have hve_vP : v * e * v⁻¹ ∈ P := s16c1_conj_mem_pCoreOf (K := H) (hVH hv) e heP
  have hevV : e * v⁻¹ * e⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hP heP) v⁻¹).mp (V.inv_mem hv)
  have h1 : v * (e * v⁻¹ * e⁻¹) ∈ V := V.mul_mem hv hevV
  have h2 : (v * e * v⁻¹) * e⁻¹ ∈ P := P.mul_mem hve_vP (P.inv_mem heP)
  rw [commutatorElement_def]
  exact Subgroup.mem_inf.mpr
    ⟨by simpa only [mul_assoc] using h1, by simpa only [mul_assoc] using h2⟩

theorem s16c1_zpowers_le_uOne {V : Subgroup G} {z : G} (hV : IsElemAbelian 2 V) (hz : z ∈ V) :
    Subgroup.zpowers z ≤ uOne V z := by
  exact le_inf (Subgroup.zpowers_le.mpr hz) (s16c1_zpowers_le_pCoreOf (hV.2 z hz))

theorem s16c1_comm_V_eOne_sup_le {V : Subgroup G} {z : G} (hV : IsElemAbelian 2 V) (hz : z ∈ V)
    (hP : pCoreOf 2 (centralizer ({z} : Set G)) ≤ normalizer (V : Set G)) :
    ⁅V, eOne V z⁆ ⊔ Subgroup.zpowers z ≤ uOne V z := by
  exact sup_le (s16c1_comm_V_eOne_le hV hz hP) (s16c1_zpowers_le_uOne hV hz)

theorem s16c1_concl1647a_bot_of (D : Data G) {V : Subgroup G} {z : G} (hV : IsElemAbelian 2 V)
    (hz : z ∈ V) (hM : D.M ≤ normalizer (V : Set G))
    (hS : IsSylowIn 2 (D.T ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G)))
    (hcore : ∀ h ∈ centralizer ({z} : Set G),
      ¬ uOne V z ⊓ conjSubgroup (uOne V z) h ≤ Subgroup.zpowers z → h ∈ D.M)
    (hv : uOne V z ≤ ⁅V, eOne V z⁆ ⊔ Subgroup.zpowers z) :
    ((uOne V z).subgroupOf (eOne V z)).Normal ∧
      (∀ h ∈ centralizer ({z} : Set G),
        ¬ uOne V z ⊓ conjSubgroup (uOne V z) h ≤ Subgroup.zpowers z → h ∈ D.M) ∧
      (∀ h ∈ centralizer ({z} : Set G),
        conjSubgroup (uOne V z) h = uOne V z ∨
          uOne V z ⊓ conjSubgroup (uOne V z) h ≤ Subgroup.zpowers z) ∧
      (⁅eOne V z, eOne V z⁆ ≤ Subgroup.zpowers z ∧
        ∀ e ∈ eOne V z, e ^ 2 ∈ Subgroup.zpowers z) ∧
      ⁅V, eOne V z⁆ ⊔ Subgroup.zpowers z = uOne V z := by
  have hP : pCoreOf 2 (centralizer ({z} : Set G)) ≤ normalizer (V : Set G) :=
    (s16c1_pCoreOf_le_M D hS).trans hM
  have hTI := s16c1_ti_of_core hM hcore
  exact ⟨s16c1_uOne_subgroupOf_normal hP, hcore, hTI,
    s16c1_phi_eOne hV hP hTI,
    le_antisymm (s16c1_comm_V_eOne_sup_le hV hz hP) hv⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
