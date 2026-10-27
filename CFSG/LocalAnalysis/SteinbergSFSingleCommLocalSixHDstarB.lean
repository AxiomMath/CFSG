module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixHDstar
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixHSecondB

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Steps

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixH_U_comm_Tplus (h1 : H1Concl φ t i) :
    ∀ u ∈ U φ i, ∀ g ∈ Tplus φ t i, g * u = u * g := by
  intro u hu g hg
  have hu' : u ∈ (center ↥(Tplus φ t i)).map (Tplus φ t i).subtype := by
    rw [h1]
    exact hu
  obtain ⟨c, hc, hcu⟩ := Subgroup.mem_map.mp hu'
  have h' : g * (c : G) = (c : G) * g :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨g, hg⟩)
  rwa [show (c : G) = u from hcu] at h'

theorem sixH_central_mem_Mhat (hS : SCSetting L K n φ t i) (h1 : H1Concl φ t i)
    (h3 : H3Concl φ t i) (h11 : H11Concl φ t i) (h12 : H12Concl φ t i) {z : G}
    (hzD : z ∈ Dstar φ t i) (hz : ∀ g ∈ Dstar φ t i, g * z = z * g) :
    z ∈ Mhat φ t i i := by
  by_contra hzM
  have hUc := sixH_U_comm_Tplus h1
  have hMM : Mc φ t i ≤ Mhat φ t i i := le_sup_left
  have hFM : F φ t ≤ Mc φ t i := NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot
  have hMD : Mhat φ t i i ≤ Dstar φ t i := le_sup_left
  have hKD : Kc φ t i.swap ≤ Dstar φ t i := le_sup_right
  have hAK : A φ i.swap ≤ Kc φ t i.swap := le_sup_left
  have hAD : A φ i.swap ≤ Dstar φ t i := hAK.trans hKD
  have hDT : Dstar φ t i ≤ Tplus φ t i := by
    rw [h11.2.2.2.2]
    exact inf_le_left.trans (le_sup_left.trans le_sup_left)
  have hD_norm : Dstar φ t i ≤ normalizer (Mhat φ t i i : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMD).mp h11.2.2.2.1
  have hAnorm : ∀ a ∈ A φ i.swap, ∀ m ∈ Mhat φ t i i, a * m * a⁻¹ ∈ Mhat φ t i i :=
    fun a ha m hm => (Subgroup.mem_normalizer_iff.mp (hD_norm (hAD ha)) m).mp hm
  have hKle : Kc φ t i.swap ≤ Mhat φ t i i ⊔ A φ i.swap :=
    sup_le le_sup_right ((inf_le_left.trans hFM).trans (hMM.trans le_sup_left))
  have hDle : Dstar φ t i ≤ Mhat φ t i i ⊔ A φ i.swap := sup_le le_sup_left hKle
  obtain ⟨m, hm, a, ha, rfl⟩ := sixH_g8_mem_sup_mul hAnorm (hDle hzD)
  have haT : a ∈ Tplus φ t i := hDT (hAD ha)
  have haZ : a ∉ Z₀ φ := by
    intro haZ
    exact hzM ((Mhat φ t i i).mul_mem hm (hMM (hFM (FullCenterTorus.ZP_le_F hS.fc haZ))))
  have hMle : Mhat φ t i i ≤ Mc φ t i := by
    intro x hx
    have hcomm : x * (m * a) = m * a * x := hz x (hMD hx)
    have e1 : a * x = m⁻¹ * (x * (m * a)) := by
      rw [hcomm]
      group
    have hp : x⁻¹ * m⁻¹ * x * m ∈ U φ i := h3.1 x hx m hm
    have hap : a * (x⁻¹ * m⁻¹ * x * m) = (x⁻¹ * m⁻¹ * x * m) * a := hUc _ hp a haT
    have e2 : a⁻¹ * x⁻¹ * a * x = a⁻¹ * (x⁻¹ * m⁻¹ * x * m) * a := by
      calc a⁻¹ * x⁻¹ * a * x = a⁻¹ * x⁻¹ * (a * x) := by group
        _ = a⁻¹ * x⁻¹ * (m⁻¹ * (x * (m * a))) := by rw [e1]
        _ = a⁻¹ * (x⁻¹ * m⁻¹ * x * m) * a := by group
    have hconj : a⁻¹ * (x⁻¹ * m⁻¹ * x * m) * a = x⁻¹ * m⁻¹ * x * m := by
      calc a⁻¹ * (x⁻¹ * m⁻¹ * x * m) * a = a⁻¹ * ((x⁻¹ * m⁻¹ * x * m) * a) := by group
        _ = a⁻¹ * (a * (x⁻¹ * m⁻¹ * x * m)) := by rw [hap]
        _ = x⁻¹ * m⁻¹ * x * m := by group
    exact (h12 a ha haZ x hx).mp (by rw [e2, hconj]; exact hp)
  have hcard : Nat.card (Mhat φ t i i) ≤ Nat.card (Mc φ t i) := Subgroup.card_le_of_le hMle
  have hM7 : Nat.card (Mhat φ t i i) = Nat.card K ^ 7 :=
    SixF.card_Mhat hS.fc i hS.ne_bot hS.eq_bot
  have hM5 : Nat.card (Mc φ t i) = Nat.card K ^ 5 := NextCores.card_M hS.fc i hS.ne_bot hS.eq_bot
  have hlt : Nat.card K ^ 5 < Nat.card K ^ 7 :=
    Nat.pow_lt_pow_right (SixG.one_lt_card_K hS.fc) (by norm_num)
  rw [hM7, hM5] at hcard
  exact absurd hcard (not_le.mpr hlt)

theorem sixH_h14_central_fixed (hS : SCSetting L K n φ t i) (h3 : H3Concl φ t i)
    (h4a : H4aConcl φ t i) {z : G} (hzM : z ∈ Mhat φ t i i)
    (hz : ∀ m ∈ Mhat φ t i i, m * z = z * m) (hzU : z ∉ U φ i) :
    ∃ x ∈ Mhat φ t i i, (∀ m ∈ Mhat φ t i i, m * x = x * m) ∧ x ∉ U φ i ∧ x ∈ Kc φ t i := by
  have ht : t * t = 1 := SixF.t_mul_t hS.fc
  have htN : t ∈ normalizer ((Mhat φ t i i : Subgroup G) : Set G) :=
    SixF.t_mem_normalizer_Mhat hS.fc i hS.ne_bot hS.eq_bot
  have hcM : ∀ m ∈ Mhat φ t i i, t⁻¹ * m * t ∈ Mhat φ t i i := fun m hm =>
    (Subgroup.mem_normalizer_iff''.mp htN m).mp hm
  have hcM' : ∀ m ∈ Mhat φ t i i, t * m * t⁻¹ ∈ Mhat φ t i i := fun m hm =>
    (Subgroup.mem_normalizer_iff.mp htN m).mp hm
  obtain ⟨z', hz'def⟩ : ∃ z', z' = t⁻¹ * z * t := ⟨_, rfl⟩
  have hz'M : z' ∈ Mhat φ t i i := hz'def ▸ hcM z hzM
  have hz'c : ∀ m ∈ Mhat φ t i i, m * z' = z' * m := by
    intro m hm
    have e := hz (t * m * t⁻¹) (hcM' m hm)
    calc m * z' = t⁻¹ * ((t * m * t⁻¹) * z) * t := by rw [hz'def]; group
      _ = t⁻¹ * (z * (t * m * t⁻¹)) * t := by rw [e]
      _ = z' * m := by rw [hz'def]; group
  have hz'U : z' ∉ U φ i := by
    intro h
    apply hzU
    have e : z = t * z' * t⁻¹ := by rw [hz'def]; group
    rw [e, sixH_h12_t_comm_U hS i h, mul_inv_cancel_right]
    exact h
  have hz'z : t⁻¹ * z' * t = z := by
    have e : t⁻¹ * z' * t = (t * t)⁻¹ * z * (t * t) := by rw [hz'def]; group
    rw [e, ht]
    group
  have hsq : z * z ∈ U φ i := by
    have : z * z ∈ closure {x : G | ∃ y ∈ Mhat φ t i i, x = y * y} := subset_closure ⟨z, hzM, rfl⟩
    rwa [h3.2] at this
  by_cases hA : z⁻¹ * t⁻¹ * z * t ∈ U φ i
  · exact ⟨z, hzM, hz, hzU, (h4a.2 z hzM).mp hA⟩
  · have hcomm : z' * z = z * z' := hz z' hz'M
    refine ⟨z * z', (Mhat φ t i i).mul_mem hzM hz'M, ?_, ?_, ?_⟩
    · intro m hm
      rw [← mul_assoc, hz m hm, mul_assoc, hz'c m hm, mul_assoc]
    · intro hxU
      apply hA
      have e : z⁻¹ * t⁻¹ * z * t = (z * z)⁻¹ * (z * z') := by rw [hz'def]; group
      rw [e]
      exact mul_mem (inv_mem hsq) hxU
    · apply (h4a.2 _ ((Mhat φ t i i).mul_mem hzM hz'M)).mp
      have e : (z * z')⁻¹ * t⁻¹ * (z * z') * t = (z * z')⁻¹ * ((t⁻¹ * z * t) * (t⁻¹ * z' * t)) := by
        group
      rw [e, ← hz'def, hz'z, hcomm]
      simp only [inv_mul_cancel]
      exact one_mem _

theorem sixH_h14_swap_swap (k : Axis) : k.swap.swap = k := by cases k <;> rfl

open scoped Pointwise in
theorem sixH_h14_Kc_decomp (h : FullCenter.FCHyp L K n φ t) (k : Axis) {x : G}
    (hx : x ∈ Kc φ t k) : ∃ a ∈ A φ k, ∃ w ∈ Wk φ t k, x = a * w := by
  have hx' : x ∈ ((A φ k : Subgroup G) : Set G) * ((F φ t ⊓ D φ t k : Subgroup G) : Set G) := by
    rw [FullCenterWeyl.K_mul h k]
    exact hx
  obtain ⟨a, ha, f, hf, rfl⟩ := Set.mem_mul.1 hx'
  have hf' : f ∈ ((F φ t ⊓ D φ t k : Subgroup G) : Set G) := hf
  rw [← FullCenterTorus.W_mul_U h k] at hf'
  obtain ⟨w, hw, u, hu, rfl⟩ := Set.mem_mul.1 hf'
  have hUsA : U φ k.swap ≤ A φ k :=
    pull_mono φ ((FullCenter.rootU_le_center (K := K) k.swap).trans
      (FullCenter.center_le_rootA (K := K) k))
  have hcomm : w * u = u * w := FullCenterTorus.comm_ZP h
    (FullCenterTorus.F_le_H h (FullCenterTorus.W_le_F k hw))
    (pull_mono φ (FullCenter.rootU_le_center (K := K) k.swap) hu)
  exact ⟨a * u, (A φ k).mul_mem ha (hUsA hu), w, hw, by rw [hcomm, mul_assoc]⟩

theorem sixH_h14_conj_comm {g p q : G} (hgg : g * g = 1)
    (h : (g⁻¹ * p * g) * q = q * (g⁻¹ * p * g)) :
    p * (g⁻¹ * q * g) = (g⁻¹ * q * g) * p := by
  have hp : g⁻¹ * (g⁻¹ * p * g) * g = p := by
    have e : g⁻¹ * (g⁻¹ * p * g) * g = (g * g)⁻¹ * p * (g * g) := by group
    rw [e, hgg]
    group
  calc p * (g⁻¹ * q * g) = (g⁻¹ * (g⁻¹ * p * g) * g) * (g⁻¹ * q * g) := by rw [hp]
    _ = g⁻¹ * ((g⁻¹ * p * g) * q) * g := by group
    _ = g⁻¹ * (q * (g⁻¹ * p * g)) * g := by rw [h]
    _ = (g⁻¹ * q * g) * (g⁻¹ * (g⁻¹ * p * g) * g) := by group
    _ = (g⁻¹ * q * g) * p := by rw [hp]

open scoped Pointwise in
theorem sixH_h14_exists_W_not_Z (h : FullCenter.FCHyp L K n φ t) (k : Axis) :
    ∃ w₁ ∈ Wk φ t k, w₁ ∉ Z₀ φ := by
  obtain ⟨y₀, hy₀, hy₀Z⟩ := FullCenterWeyl.exists_Fi_not_ZP h k
  have hy₀' : y₀ ∈ ((Wk φ t k : Subgroup G) : Set G) * ((U φ k.swap : Subgroup G) : Set G) := by
    rw [FullCenterTorus.W_mul_U h k]
    exact hy₀
  obtain ⟨w₁, hw₁, u₁, hu₁, rfl⟩ := Set.mem_mul.1 hy₀'
  refine ⟨w₁, hw₁, fun hZ => hy₀Z ?_⟩
  exact (Z₀ φ).mul_mem hZ (pull_mono φ (FullCenter.rootU_le_center (K := K) k.swap) hu₁)

theorem sixH_h14_v_one (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    {v w' : G} (hv : v ∈ U φ i.swap) (hw' : w' ∈ Wk φ t i)
    (hc : ∀ m ∈ Mhat φ t i i, m * (v * w') = (v * w') * m) : v = 1 := by
  by_contra hv1
  have h2b := sixH_h2b hS hM2
  have hgg : w φ i * w φ i = 1 := FullCenterWeyl.w_mul_self (φ := φ) i
  obtain ⟨w₁, hw₁, hw₁Z⟩ := sixH_h14_exists_W_not_Z hS.fc i.swap
  have hw₁M : w₁ ∈ Mc φ t i :=
    NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot (FullCenterTorus.W_le_F i.swap hw₁)
  have hyM : (w φ i)⁻¹ * w₁ * w φ i ∈ Mhat φ t i i :=
    mem_sup_right (Subgroup.mem_map.mpr ⟨w₁, hw₁M, by simp [MulAut.conj_apply]⟩)
  have hw'V : w' ∈ Vtor φ t i i := RootStandard.W_le_V hS.fc i hS.ne_bot hS.eq_bot i hw'
  have hE : (w φ i)⁻¹ * w' * w φ i ∈ Vtor φ t i i := h2b.1 w' hw'V
  have hEc : ((w φ i)⁻¹ * w' * w φ i) * w₁ = w₁ * ((w φ i)⁻¹ * w' * w φ i) :=
    RootStandard.V_comm_W_swap hS.fc i hS.ne_bot hS.eq_bot hE hw₁
  have hw'y : w' * ((w φ i)⁻¹ * w₁ * w φ i) = ((w φ i)⁻¹ * w₁ * w φ i) * w' :=
    sixH_h14_conj_comm hgg hEc
  have hcy := hc _ hyM
  have hvy : v * ((w φ i)⁻¹ * w₁ * w φ i) = ((w φ i)⁻¹ * w₁ * w φ i) * v := by
    have e : ((w φ i)⁻¹ * w₁ * w φ i) * v * w' = v * ((w φ i)⁻¹ * w₁ * w φ i) * w' := by
      calc ((w φ i)⁻¹ * w₁ * w φ i) * v * w'
          = ((w φ i)⁻¹ * w₁ * w φ i) * (v * w') := by group
        _ = v * w' * ((w φ i)⁻¹ * w₁ * w φ i) := hcy
        _ = v * (w' * ((w φ i)⁻¹ * w₁ * w φ i)) := by group
        _ = v * (((w φ i)⁻¹ * w₁ * w φ i) * w') := by rw [hw'y]
        _ = v * ((w φ i)⁻¹ * w₁ * w φ i) * w' := by group
    exact (mul_right_cancel e).symm
  have hv' : w₁ * ((w φ i)⁻¹ * v * w φ i) = ((w φ i)⁻¹ * v * w φ i) * w₁ :=
    sixH_h14_conj_comm hgg hvy.symm
  obtain ⟨hvA, hvZ⟩ := (sixH_s2_weyl i).2 v hv hv1
  have hmem : (w φ i)⁻¹ * v * w φ i ∈ A φ i ⊓ centralizer ({w₁} : Set G) :=
    ⟨hvA, Subgroup.mem_centralizer_singleton_iff.mpr hv'.symm⟩
  rw [(FullCenterWeyl.centers_of_ne_bot hS.fc i hS.ne_bot).2.2 w₁
    (FullCenterTorus.W_le_Fi hS.fc i.swap hw₁) hw₁Z] at hmem
  exact hvZ hmem

theorem sixH_h14_central_K (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h2d : H2dConcl φ t i) {x : G} (hxK : x ∈ Kc φ t i)
    (hxc : ∀ m ∈ Mhat φ t i i, m * x = x * m) : x ∈ U φ i := by
  have hFM : F φ t ≤ Mhat φ t i i :=
    (NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot).trans le_sup_left
  obtain ⟨a, ha, w', hw', rfl⟩ := sixH_h14_Kc_decomp hS.fc i hxK
  have hw'F : w' ∈ F φ t := FullCenterTorus.W_le_F i hw'
  obtain ⟨y₀, hy₀, hy₀Z⟩ := FullCenterWeyl.exists_Fi_not_ZP hS.fc i.swap
  have hwy : w' * y₀ = y₀ * w' := FullCenterTorus.F_comm hS.fc hw'F hy₀.1
  have hay : y₀ * a = a * y₀ := by
    have e : y₀ * a * w' = a * y₀ * w' := by
      calc y₀ * a * w' = y₀ * (a * w') := by group
        _ = a * w' * y₀ := hxc y₀ (hFM hy₀.1)
        _ = a * (w' * y₀) := by group
        _ = a * (y₀ * w') := by rw [hwy]
        _ = a * y₀ * w' := by group
    exact mul_right_cancel e
  have haZ : a ∈ Z₀ φ := by
    have hmem : a ∈ A φ i ⊓ centralizer ({y₀} : Set G) :=
      ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr hay.symm⟩
    rwa [(FullCenterWeyl.centers_of_ne_bot hS.fc i hS.ne_bot).2.2 y₀ hy₀ hy₀Z] at hmem
  obtain ⟨u, hu, v, hv, rfl⟩ := RootStandard.exists_U_mul_U i haZ
  have hZu : u ∈ Z₀ φ := pull_mono φ (FullCenter.rootU_le_center (K := K) i) hu
  have hZv : v ∈ Z₀ φ := pull_mono φ (FullCenter.rootU_le_center (K := K) i.swap) hv
  have huv : u * v = v * u := FullCenterTorus.comm_ZP hS.fc
    (FullCenterTorus.F_le_H hS.fc (FullCenterTorus.ZP_le_F hS.fc hZu)) hZv
  have hw'' : u * w' ∈ Wk φ t i := (Wk φ t i).mul_mem (FullCenterTorus.U_le_W hS.fc i hu) hw'
  have hxeq : u * v * w' = v * (u * w') := by
    calc u * v * w' = v * u * w' := by rw [huv]
      _ = v * (u * w') := by group
  have hv1 : v = 1 := by
    refine sixH_h14_v_one hS hM2 hv hw'' (fun m hm => ?_)
    rw [← hxeq]
    exact hxc m hm
  subst hv1
  have hxV : u * 1 * w' ∈ Vtor φ t i i := by
    rw [mul_one]
    exact RootStandard.W_le_V hS.fc i hS.ne_bot hS.eq_bot i hw''
  have hVM : Vtor φ t i i ≤ Mhat φ t i i := inf_le_left.trans le_sup_left
  have hcen : (⟨u * 1 * w', hxV⟩ : ↥(Vtor φ t i i)) ∈ center ↥(Vtor φ t i i) :=
    Subgroup.mem_center_iff.mpr fun m => Subtype.ext (hxc (m : G) (hVM m.2))
  have hmem : u * 1 * w' ∈ (center ↥(Vtor φ t i i)).map (Vtor φ t i i).subtype :=
    Subgroup.mem_map.mpr ⟨_, hcen, rfl⟩
  rwa [h2d.1] at hmem

theorem sixH_h14 (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1 : H1Concl φ t i) (h2d : H2dConcl φ t i) (h3 : H3Concl φ t i) (h4a : H4aConcl φ t i) :
    H14Concl φ t i := by
  unfold H14Concl
  have hMT : Mhat φ t i i ≤ Tplus φ t i :=
    (SixF.Mhat_le_P₁ hS.fc i hS.ne_bot hS.eq_bot).trans
      (le_sup_right.trans (le_sup_left.trans le_sup_left))
  have hUM : U φ i ≤ Mhat φ t i i := by
    intro u hu
    have hu' : u ∈ closure {x : G | ∃ y ∈ Mhat φ t i i, x = y * y} := by
      rw [h3.2]
      exact hu
    exact (Subgroup.closure_le (Mhat φ t i i)).mpr
      (by rintro _ ⟨y, hy, rfl⟩; exact mul_mem hy hy) hu'
  apply le_antisymm
  · intro z hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
    have hzc : ∀ m ∈ Mhat φ t i i, m * (c : G) = (c : G) * m := fun m hm =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨m, hm⟩)
    by_contra hzU
    obtain ⟨x, -, hxc, hxU, hxK⟩ := sixH_h14_central_fixed hS h3 h4a c.2 hzc hzU
    exact hxU (sixH_h14_central_K hS hM2 h2d hxK hxc)
  · intro u hu
    exact Subgroup.mem_map.mpr ⟨⟨u, hUM hu⟩, Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (sixH_U_comm_Tplus h1 u hu (g : G) (hMT g.2)), rfl⟩

theorem sixH_h15 (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1 : H1Concl φ t i) (h11 : H11Concl φ t i) (h12 : H12Concl φ t i) (h14 : H14Concl φ t i) : (center ↥(Dstar φ t i)).map (Dstar φ t i).subtype = U φ i := by
  have h3 := sixH_h3 hS hM2 h1 (sixH_h2a hS hM2 h1) (sixH_h2b hS hM2)
  have hMD : Mhat φ t i i ≤ Dstar φ t i := le_sup_left
  have hDT : Dstar φ t i ≤ Tplus φ t i := by
    rw [h11.2.2.2.2]
    exact inf_le_left.trans (le_sup_left.trans le_sup_left)
  have hUM : ∀ u ∈ U φ i, u ∈ Mhat φ t i i := by
    intro u hu
    rw [← h14] at hu
    obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.mp hu
    exact c.2
  ext u
  constructor
  · intro hu
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hu
    have hzc : ∀ g ∈ Dstar φ t i, g * (z : G) = (z : G) * g :=
      fun g hg => congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
    by_cases hzM : (z : G) ∈ Mhat φ t i i
    · have hcM : (⟨(z : G), hzM⟩ : ↥(Mhat φ t i i)) ∈ center ↥(Mhat φ t i i) :=
        Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hzc (g : G) (hMD g.2))
      rw [← h14]
      exact Subgroup.mem_map.mpr ⟨_, hcM, rfl⟩
    · exact absurd (sixH_central_mem_Mhat hS h1 h3 h11 h12 z.2 hzc) hzM
  · intro hu
    have huD : u ∈ Dstar φ t i := hMD (hUM u hu)
    exact Subgroup.mem_map.mpr
      ⟨⟨u, huD⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext
        (sixH_U_comm_Tplus h1 u hu (g : G) (hDT g.2)), rfl⟩

theorem sixH_h16_quot_elem {Γ : Type} [Group Γ] {P N H : Subgroup Γ} [(N.subgroupOf P).Normal]
    (hHP : H ≤ P) (hcomm : ∀ a ∈ H, ∀ b ∈ H, a⁻¹ * b⁻¹ * a * b ∈ N) (hsq : ∀ a ∈ H, a * a ∈ N) :
    IsElementaryAbelian 2 ((H.subgroupOf P).map (QuotientGroup.mk' (N.subgroupOf P))) := by
  have hmem : ∀ a : ↥((H.subgroupOf P).map (QuotientGroup.mk' (N.subgroupOf P))),
      ∃ h : ↥P, (h : Γ) ∈ H ∧
        QuotientGroup.mk' (N.subgroupOf P) h = (a : ↥P ⧸ N.subgroupOf P) := by
    intro a
    obtain ⟨h, hh, hha⟩ := Subgroup.mem_map.mp a.2
    exact ⟨h, Subgroup.mem_subgroupOf.mp hh, hha⟩
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · obtain ⟨h₁, hh₁, h₁a⟩ := hmem a
    obtain ⟨h₂, hh₂, h₂b⟩ := hmem b
    apply Subtype.ext
    show (a : ↥P ⧸ N.subgroupOf P) * (b : ↥P ⧸ N.subgroupOf P) = b * a
    rw [← h₁a, ← h₂b, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    have e := hcomm _ hh₂ _ hh₁
    simpa [mul_assoc] using e
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
    obtain ⟨h₁, hh₁, h₁a⟩ := hmem a
    apply Subtype.ext
    show (a : ↥P ⧸ N.subgroupOf P) ^ 2 = 1
    rw [← h₁a, ← map_pow, QuotientGroup.mk'_apply, ← QuotientGroup.mk_one, QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    have e := N.inv_mem (hsq _ hh₁)
    simpa [sq, mul_inv_rev] using e

theorem sixH_h16_cover {Γ : Type} [Group Γ] [Finite Γ] {P N B₁ B₂ H : Subgroup Γ}
    [(N.subgroupOf P).Normal] (hmax : SixG.MNMaximal P B₁ B₂ P N) (hNB₁ : N ≤ B₁)
    (hNB₂ : N ≤ B₂) (hHP : H ≤ P) (hcomm : ∀ a ∈ H, ∀ b ∈ H, a⁻¹ * b⁻¹ * a * b ∈ N)
    (hsq : ∀ a ∈ H, a * a ∈ N) : H ≤ B₁ ∨ H ≤ B₂ := by
  haveI : IsElementaryAbelian 2 ((H.subgroupOf P).map (QuotientGroup.mk' (N.subgroupOf P))) :=
    sixH_h16_quot_elem hHP hcomm hsq
  haveI : Finite (↥P ⧸ N.subgroupOf P) :=
    Finite.of_surjective (QuotientGroup.mk : ↥P → _) QuotientGroup.mk_surjective
  have hle : (H.subgroupOf P).map (QuotientGroup.mk' (N.subgroupOf P)) ≤
      (P.subgroupOf P).map (QuotientGroup.mk' (N.subgroupOf P)) :=
    Subgroup.map_mono fun x _ => Subgroup.mem_subgroupOf.mpr x.2
  obtain ⟨Sg, hS0, hSg⟩ := sixH_g6_exists_maximal hle
  have hcov : ∀ B : Subgroup Γ, N ≤ B →
      Sg = (B.subgroupOf P).map (QuotientGroup.mk' (N.subgroupOf P)) → H ≤ B := by
    intro B hNB hSB y hy
    have hyP : y ∈ P := hHP hy
    have hmem : (QuotientGroup.mk' (N.subgroupOf P) ⟨y, hyP⟩ : ↥P ⧸ N.subgroupOf P) ∈
        (B.subgroupOf P).map (QuotientGroup.mk' (N.subgroupOf P)) := by
      rw [← hSB]
      exact hS0 (Subgroup.mem_map.mpr ⟨⟨y, hyP⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩)
    obtain ⟨b, hb, hby⟩ := sixH_g7_quot_mem hyP hmem
    have e : y = b * (b⁻¹ * y) := by group
    rw [e]
    exact B.mul_mem hb (hNB hby)
  rcases (hmax Sg).mp hSg with h | h
  · exact Or.inl (hcov B₁ hNB₁ h)
  · exact Or.inr (hcov B₂ hNB₂ h)

theorem sixH_h16_uniq (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1 : H1Concl φ t i) (h3 : H3Concl φ t i) (h9 : H9Concl φ t i) (h11 : H11Concl φ t i)
    (h13 : H13Concl φ t i) {g : G} (hgT : g ∈ Tplus φ t i)
    (hgD : g ∈ normalizer (Dstar φ t i : Set G)) : g ∈ normalizer (Mhat φ t i i : Set G) := by
  obtain ⟨hNU, hmax⟩ := h13
  haveI := hNU
  have hUc := sixH_U_comm_Tplus h1
  have hUM : U φ i ≤ Mc φ t i := sixH_h13_U_le_Mc hS hM2
  have hMM : Mc φ t i ≤ Mhat φ t i i := le_sup_left
  have hMD : Mhat φ t i i ≤ Dstar φ t i := le_sup_left
  have hFM : F φ t ≤ Mc φ t i := NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot
  have hsqU : ∀ m ∈ Mhat φ t i i, m * m ∈ U φ i := by
    intro m hm
    have : m * m ∈ closure {x : G | ∃ y ∈ Mhat φ t i i, x = y * y} := subset_closure ⟨m, hm, rfl⟩
    rwa [h3.2] at this
  have hKn : ∀ a ∈ Tplus φ t i, ∀ n ∈ Kc φ t i.swap, a * n * a⁻¹ ∈ Kc φ t i.swap := fun a ha n hn =>
    (Subgroup.mem_normalizer_iff.mp
      (mem_inf.mp (mem_inf.mp (SixG.Tplus_le_normalizers hS.fc i hS.ne_bot hS.eq_bot hM2 ha)).1).1
      n).mp hn
  have hMn : ∀ a ∈ Tplus φ t i, ∀ n ∈ Mc φ t i, a * n * a⁻¹ ∈ Mc φ t i := fun a ha n hn =>
    (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normal_subgroupOf_iff_le_normalizer h9.1).mp h9.2.1 ha) n).mp hn
  have key : ∀ g' ∈ Tplus φ t i, g' ∈ normalizer (Dstar φ t i : Set G) →
      ∀ m ∈ Mhat φ t i i, g'⁻¹ * m * g' ∈ Mhat φ t i i := by
    intro g' hg'T hg'D
    obtain ⟨H, hHdef⟩ : ∃ H : Subgroup G, H = (Mhat φ t i i).map (MulAut.conj g'⁻¹).toMonoidHom :=
      ⟨_, rfl⟩
    have hHmem : ∀ a, a ∈ H ↔ g' * a * g'⁻¹ ∈ Mhat φ t i i := fun a => by
      rw [hHdef]
      exact FullCenterWeyl.mem_map_conj_inv
    have hconj : ∀ u ∈ U φ i, g'⁻¹ * u * g' = u := fun u hu => by
      rw [hUc u hu g'⁻¹ (inv_mem hg'T), inv_mul_cancel_right]
    have hHD : H ≤ Dstar φ t i := fun a ha =>
      (Subgroup.mem_normalizer_iff.mp hg'D a).mpr (hMD ((hHmem a).mp ha))
    have hcomm : ∀ a ∈ H, ∀ b ∈ H, a⁻¹ * b⁻¹ * a * b ∈ U φ i := by
      intro a ha b hb
      have hc := h3.1 _ ((hHmem a).mp ha) _ ((hHmem b).mp hb)
      have e : a⁻¹ * b⁻¹ * a * b =
          g'⁻¹ * ((g' * a * g'⁻¹)⁻¹ * (g' * b * g'⁻¹)⁻¹ * (g' * a * g'⁻¹) * (g' * b * g'⁻¹)) * g' := by
        group
      rw [e, hconj _ hc]
      exact hc
    have hsq : ∀ a ∈ H, a * a ∈ U φ i := by
      intro a ha
      have hc := hsqU _ ((hHmem a).mp ha)
      have e : a * a = g'⁻¹ * ((g' * a * g'⁻¹) * (g' * a * g'⁻¹)) * g' := by group
      rw [e, hconj _ hc]
      exact hc
    have hHle : H ≤ Mhat φ t i i := by
      rcases sixH_h16_cover hmax (hUM.trans hMM) (hUM.trans le_sup_left) hHD hcomm hsq with h | h
      · exact h
      · exfalso
        have hMhatB : ∀ q ∈ Mhat φ t i i, q ∈ Mc φ t i ⊔ Kc φ t i.swap := by
          intro q hq
          have hqH : g'⁻¹ * q * g' ∈ H := by
            rw [hHmem]
            have e : g' * (g'⁻¹ * q * g') * g'⁻¹ = q := by group
            rw [e]
            exact hq
          have := RootAxisTwoCore.conj_mem_sup (g := g') (H₁ := Mc φ t i) (H₂ := Kc φ t i.swap)
            (hMn g' hg'T) (hKn g' hg'T) (h hqH)
          have e : g' * (g'⁻¹ * q * g') * g'⁻¹ = q := by group
          rwa [e] at this
        have hMhatM : Mhat φ t i i ≤ Mc φ t i := by
          intro q hq
          have hq' : q ∈ Kc φ t i.swap ⊔ Mc φ t i := by
            rw [sup_comm]
            exact hMhatB q hq
          obtain ⟨k, hk, m, hm, rfl⟩ := sixH_g8_mem_sup_mul
            (fun a ha n hn => hKn a (h9.1 ha) n hn) hq'
          have hkM : k ∈ Mhat φ t i i := by
            have := (Mhat φ t i i).mul_mem hq (inv_mem (hMM hm))
            rwa [mul_inv_cancel_right] at this
          have hkF : k ∈ F φ t ⊓ D φ t i.swap := by
            rw [← h11.2.1]
            exact mem_inf.mpr ⟨hkM, hk⟩
          exact (Mc φ t i).mul_mem (hFM (mem_inf.mp hkF).1) hm
        have hcard : Nat.card (Mhat φ t i i) ≤ Nat.card (Mc φ t i) :=
          Subgroup.card_le_of_le hMhatM
        have hM7 : Nat.card (Mhat φ t i i) = Nat.card K ^ 7 :=
          SixF.card_Mhat hS.fc i hS.ne_bot hS.eq_bot
        have hM5 : Nat.card (Mc φ t i) = Nat.card K ^ 5 :=
          NextCores.card_M hS.fc i hS.ne_bot hS.eq_bot
        have hlt : Nat.card K ^ 5 < Nat.card K ^ 7 :=
          Nat.pow_lt_pow_right (SixG.one_lt_card_K hS.fc) (by norm_num)
        rw [hM7, hM5] at hcard
        exact absurd hcard (not_le.mpr hlt)
    intro m hm
    exact hHle ((hHmem _).mpr (by
      have e : g' * (g'⁻¹ * m * g') * g'⁻¹ = m := by group
      rw [e]
      exact hm))
  refine RootAxisTwoCore.mem_normalizer_of_conj_le fun q hq => ?_
  have := key g⁻¹ (inv_mem hgT) (inv_mem hgD) q hq
  simpa using this

theorem sixH_h16_Tplus_normalizes_S (h8 : H8Concl φ t i) :
    Tplus φ t i ≤ normalizer (S φ t i : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (by rw [← h8.2.2.2.1]; exact le_sup_left)).mp
    h8.2.2.2.2.2

theorem sixH_h16_Tbar_normalizes_D (hS : SCSetting L K n φ t i) (h8 : H8Concl φ t i)
    (h11 : H11Concl φ t i) : Tbar φ t i ≤ normalizer (Dstar φ t i : Set G) := by
  intro g hg
  have hT : g ∈ normalizer (T₁ φ t i : Set G) :=
    (sup_le Subgroup.le_normalizer
      (NextCores.T₂_le_normalizer_T₁ hS.fc i hS.ne_bot hS.eq_bot) : Tbar φ t i ≤ _) hg
  have hSn : g ∈ normalizer (S φ t i : Set G) :=
    sixH_h16_Tplus_normalizes_S h8 ((le_sup_left : Tbar φ t i ≤ Tplus φ t i) hg)
  rw [h11.2.2.2.2]
  exact RootAxisTwoCore.mem_normalizer_of_conj_le fun q hq =>
    mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hT q).mp (mem_inf.mp hq).1,
      (Subgroup.mem_normalizer_iff.mp hSn q).mp (mem_inf.mp hq).2⟩

theorem sixH_h16_zpowers_two (ht : t * t = 1) {a : G} (ha : a ∈ zpowers t) : a = 1 ∨ a = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact RootAxisTwoCore.zpow_eq_one_or_eq ht k

theorem sixH_h16_Mhat_le_S (k : Axis) : Mhat φ t i k ≤ S φ t i := by
  cases k
  · exact le_sup_left
  · exact le_sup_right

theorem sixH_h16_Kstar_le_D (h4a : H4aConcl φ t i) : Kstar φ t ≤ Dstar φ t i := by
  refine sup_le ?_ ?_
  · rcases SingleComm.eq_or_eq_swap i Axis.one with rfl | h
    · exact h4a.1.trans le_sup_left
    · rw [h]
      exact le_sup_right
  · rcases SingleComm.eq_or_eq_swap i Axis.two with rfl | h
    · exact h4a.1.trans le_sup_left
    · rw [h]
      exact le_sup_right

theorem sixH_h16_Cstar_le_Mhat (hS : SCSetting L K n φ t i) :
    Cstar φ t i ≤ Mhat φ t i i.swap :=
  sup_le le_sup_left
    ((Subgroup.map_mono (NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot)).trans le_sup_right)

theorem sixH_h16_Astar_le_S (hS : SCSetting L K n φ t i) (h4a : H4aConcl φ t i) :
    Astar φ t i ≤ S φ t i := by
  have hCM := sixH_h16_Cstar_le_Mhat hS
  have hMS : Mc φ t i ≤ S φ t i :=
    (le_sup_left : Mc φ t i ≤ Mhat φ t i i).trans (sixH_h16_Mhat_le_S i)
  have hFwS : Fw φ t i.swap ≤ S φ t i :=
    ((le_sup_right : Fw φ t i.swap ≤ Cstar φ t i).trans hCM).trans (sixH_h16_Mhat_le_S i.swap)
  have hK : ∀ k : Axis, Kc φ t k ≤ S φ t i := by
    intro k
    rcases SingleComm.eq_or_eq_swap i k with h | h
    · rw [h]
      exact h4a.1.trans (sixH_h16_Mhat_le_S i)
    · rw [h]
      exact (SixG.K_le_Cstar hS.fc i hS.ne_bot hS.eq_bot).trans
        (hCM.trans (sixH_h16_Mhat_le_S i.swap))
  exact sup_le (sup_le hMS (sup_le (hK Axis.one) (hK Axis.two))) hFwS

theorem sixH_h16_T₂_inf_S (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h4a : H4aConcl φ t i) (h8 : H8Concl φ t i) {z : G} (hz : z ∈ T₂ φ t i.swap)
    (hzS : z ∈ S φ t i) : z ∈ Astar φ t i := by
  have ht : t * t = 1 := SixF.t_mul_t hS.fc
  have hAT := SixG.Astar_sup_t hS.fc i hS.ne_bot hS.eq_bot
  have hAS := sixH_h16_Astar_le_S hS h4a
  have hz' : z ∈ Astar φ t i ⊔ zpowers t := by
    rw [hAT.1]
    exact hz
  have hnorm := SixG.normalIn_Astar hS.fc i hS.ne_bot hS.eq_bot hM2
  have hAn : Tplus φ t i ≤ normalizer (Astar φ t i : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hnorm.1).mp hnorm.2.1
  have hzp : zpowers t ≤ Tplus φ t i := by
    rw [← h8.2.2.2.1]
    exact le_sup_right
  obtain ⟨a, ha, a₀, ha₀, hza⟩ := sixH_g8_mem_sup_mul
    (fun b hb n hn => (Subgroup.mem_normalizer_iff.mp (hAn (hzp hb)) n).mp hn) hz'
  rcases sixH_h16_zpowers_two ht ha₀ with h0 | h0
  · rw [hza, h0, mul_one]
    exact ha
  · have htS : t ∈ S φ t i := by
      have := (S φ t i).mul_mem ((S φ t i).inv_mem (hAS ha)) hzS
      rwa [hza, h0, inv_mul_cancel_left] at this
    have h1 : t ∈ S φ t i ⊓ zpowers t := mem_inf.mpr ⟨htS, mem_zpowers t⟩
    rw [h8.2.2.2.2.1, Subgroup.mem_bot] at h1
    rw [hza, h0.trans h1, mul_one]
    exact ha

open scoped Pointwise in
theorem sixH_h16_omega (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h4a : H4aConcl φ t i) (h8 : H8Concl φ t i) (h11 : H11Concl φ t i) {x : G}
    (hxT : x ∈ Tbar φ t i) (hxS : x ∈ S φ t i) :
    ∃ d ∈ Dstar φ t i, ∃ f ∈ Fw φ t i.swap, x = d * f := by
  have ht : t * t = 1 := SixF.t_mul_t hS.fc
  have hSn := sixH_h16_Tplus_normalizes_S h8
  have hzp : zpowers t ≤ Tplus φ t i := by
    rw [← h8.2.2.2.1]
    exact le_sup_right
  have hxT' : x ∈ (T₁ φ t i : Set G) * (T₂ φ t i.swap : Set G) := by
    rw [NextCores.Tbar_mul hS.fc i hS.ne_bot hS.eq_bot]
    exact hxT
  obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_mul.1 hxT'
  have hyTp : y ∈ Tplus φ t i :=
    (le_sup_left : Tbar φ t i ≤ Tplus φ t i) ((le_sup_left : T₁ φ t i ≤ Tbar φ t i) hy)
  have hySup : y ∈ S φ t i ⊔ zpowers t := by
    rw [h8.2.2.2.1]
    exact hyTp
  obtain ⟨s, hs, a, ha, hya⟩ := sixH_g8_mem_sup_mul
    (fun b hb n hn => (Subgroup.mem_normalizer_iff.mp (hSn (hzp hb)) n).mp hn) hySup
  have htT₁ : t ∈ T₁ φ t i :=
    (le_sup_left : R φ t i ≤ T₁ φ t i) (mem_sup_left (mem_sup_right (mem_zpowers t)))
  have htT₂ : t ∈ T₂ φ t i.swap :=
    (SixG.Astar_sup_t hS.fc i hS.ne_bot hS.eq_bot).1.le (mem_sup_right (mem_zpowers t))
  have hA : ∃ d ∈ Dstar φ t i, ∃ z' ∈ Astar φ t i, x = d * z' := by
    rcases sixH_h16_zpowers_two ht ha with h0 | h0
    · have hyS : y ∈ S φ t i := by
        rw [hya, h0, mul_one]
        exact hs
      have hyD : y ∈ Dstar φ t i := by
        rw [h11.2.2.2.2]
        exact mem_inf.mpr ⟨hy, hyS⟩
      refine ⟨y, hyD, z, sixH_h16_T₂_inf_S hS hM2 h4a h8 hz ?_, hyz.symm⟩
      have := (S φ t i).mul_mem ((S φ t i).inv_mem hyS) hxS
      rwa [← hyz, inv_mul_cancel_left] at this
    · have hyt : y * t ∈ S φ t i := by
        rw [hya, h0, mul_assoc, ht, mul_one]
        exact hs
      have hd : y * t ∈ Dstar φ t i := by
        rw [h11.2.2.2.2]
        exact mem_inf.mpr ⟨(T₁ φ t i).mul_mem hy htT₁, hyt⟩
      have hz'T : t * z ∈ T₂ φ t i.swap := (T₂ φ t i.swap).mul_mem htT₂ hz
      have hxyz : x = (y * t) * (t * z) :=
        calc x = y * z := hyz.symm
          _ = y * (t * t) * z := by rw [ht, mul_one]
          _ = (y * t) * (t * z) := by group
      have hz'S : t * z ∈ S φ t i := by
        have := (S φ t i).mul_mem ((S φ t i).inv_mem hyt) hxS
        rwa [hxyz, inv_mul_cancel_left] at this
      exact ⟨y * t, hd, t * z, sixH_h16_T₂_inf_S hS hM2 h4a h8 hz'T hz'S, hxyz⟩
  obtain ⟨d, hd, z', hz', hx⟩ := hA
  have hz'm : z' ∈ ((Mc φ t i : Subgroup G) : Set G) * (Kstar φ t : Set G) *
      (Fw φ t i.swap : Set G) := by
    rw [SixG.Astar_mul hS.fc i hS.ne_bot hS.eq_bot]
    exact hz'
  obtain ⟨_, ⟨m, hm, k, hk, rfl⟩, f, hf, rfl⟩ := hz'm
  have hMD : Mc φ t i ≤ Dstar φ t i := le_sup_left.trans le_sup_left
  exact ⟨d * m * k, (Dstar φ t i).mul_mem ((Dstar φ t i).mul_mem hd (hMD hm))
    (sixH_h16_Kstar_le_D h4a hk), f, hf, by rw [hx]; group⟩

theorem sixH_h16_Kj_conj (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    {a : G} (ha : a ∈ Tplus φ t i) {n : G} (hn : n ∈ Kc φ t i.swap) :
    a * n * a⁻¹ ∈ Kc φ t i.swap :=
  (Subgroup.mem_normalizer_iff.mp
    (mem_inf.mp (mem_inf.mp (SixG.Tplus_le_normalizers hS.fc i hS.ne_bot hS.eq_bot hM2 ha)).1).1
    n).mp hn

theorem sixH_h16_Cstar_conj (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    {a : G} (ha : a ∈ Tplus φ t i) {n : G} (hn : n ∈ Cstar φ t i) :
    a * n * a⁻¹ ∈ Cstar φ t i :=
  (Subgroup.mem_normalizer_iff.mp
    (mem_inf.mp (SixG.Tplus_le_normalizers hS.fc i hS.ne_bot hS.eq_bot hM2 ha)).2 n).mp hn

theorem sixH_h16_M_conj (h9 : H9Concl φ t i) {a : G} (ha : a ∈ Tplus φ t i) {n : G}
    (hn : n ∈ Mc φ t i) : a * n * a⁻¹ ∈ Mc φ t i :=
  (Subgroup.mem_normalizer_iff.mp
    ((Subgroup.normal_subgroupOf_iff_le_normalizer h9.1).mp h9.2.1 ha) n).mp hn

theorem sixH_h16_Mhat_le_Tplus (hS : SCSetting L K n φ t i) :
    Mhat φ t i i ≤ Tplus φ t i :=
  (SixF.Mhat_le_P₁ hS.fc i hS.ne_bot hS.eq_bot).trans
    (le_sup_right.trans (le_sup_left.trans le_sup_left))

theorem sixH_h16_Cstar_le_Tplus (hS : SCSetting L K n φ t i) :
    Cstar φ t i ≤ Tplus φ t i :=
  (SixG.Cstar_le_Astar i).trans
    ((SixG.Astar_le_T₂ hS.fc i hS.ne_bot hS.eq_bot).trans (SixG.T₂_le_Tplus i))

theorem sixH_h16_D_sq (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h3 : H3Concl φ t i) (h11 : H11Concl φ t i) {d : G} (hd : d ∈ Dstar φ t i) :
    d * d ∈ Mc φ t i := by
  have hUM := sixH_h13_U_le_Mc hS hM2
  have hFM : F φ t ≤ Mc φ t i := NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot
  have hD_norm : Dstar φ t i ≤ normalizer (Mhat φ t i i : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp h11.2.2.2.1
  have hKD : Kc φ t i.swap ≤ Dstar φ t i := le_sup_right
  have hMT := sixH_h16_Mhat_le_Tplus hS
  have hsqU : ∀ m ∈ Mhat φ t i i, m * m ∈ U φ i := by
    intro m hm
    have : m * m ∈ closure {x : G | ∃ y ∈ Mhat φ t i i, x = y * y} := subset_closure ⟨m, hm, rfl⟩
    rwa [h3.2] at this
  obtain ⟨m, hm, k, hk, rfl⟩ := sixH_g8_mem_sup_mul (N := Mhat φ t i i) (A := Kc φ t i.swap)
    (fun a ha n hn => (Subgroup.mem_normalizer_iff.mp (hD_norm (hKD ha)) n).mp hn) hd
  have hkk : k * k = 1 :=
    SingleComm.K_sq hS.fc i.swap (fun w hw => SingleComm.sq_W_swap hS.fc i hS.ne_bot hS.eq_bot hw)
      hk
  have hcM : m⁻¹ * (k * m * k⁻¹) ∈ Mhat φ t i i :=
    (Mhat φ t i i).mul_mem ((Mhat φ t i i).inv_mem hm)
      ((Subgroup.mem_normalizer_iff.mp (hD_norm (hKD hk)) m).mp hm)
  have hcK : m⁻¹ * k * m * k⁻¹ ∈ Kc φ t i.swap := by
    have := (Kc φ t i.swap).mul_mem (sixH_h16_Kj_conj hS hM2 ((sixH_h16_Mhat_le_Tplus hS)
      ((Mhat φ t i i).inv_mem hm)) hk) ((Kc φ t i.swap).inv_mem hk)
    simpa [mul_assoc] using this
  have hcF : m⁻¹ * (k * m * k⁻¹) ∈ F φ t ⊓ D φ t i.swap := by
    rw [← h11.2.1]
    refine mem_inf.mpr ⟨hcM, ?_⟩
    simpa [mul_assoc] using hcK
  have e : m * k * (m * k) = (m * m) * (m⁻¹ * (k * m * k⁻¹)) * (k * k) := by group
  rw [e, hkk, mul_one]
  exact (Mc φ t i).mul_mem (hUM (hsqU m hm)) (hFM (mem_inf.mp hcF).1)

theorem sixH_h16_comm (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h6 : H6Concl φ t i) (h8 : H8Concl φ t i) (h9 : H9Concl φ t i) (h11 : H11Concl φ t i)
    {f d : G} (hf : f ∈ Cstar φ t i) (hfN : f ∈ normalizer (Mhat φ t i i : Set G))
    (hd : d ∈ Dstar φ t i) : f⁻¹ * d⁻¹ * f * d ∈ Mc φ t i := by
  have hD_norm : Dstar φ t i ≤ normalizer (Mhat φ t i i : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp h11.2.2.2.1
  have hKD : Kc φ t i.swap ≤ Dstar φ t i := le_sup_right
  have hMT := sixH_h16_Mhat_le_Tplus hS
  have hKT : Kc φ t i.swap ≤ Tplus φ t i :=
    (SixG.K_le_T₂ hS.fc i.swap).trans (SixG.T₂_le_Tplus i)
  obtain ⟨m, hm, k, hk, rfl⟩ := sixH_g8_mem_sup_mul (N := Mhat φ t i i) (A := Kc φ t i.swap)
    (fun a ha n hn => (Subgroup.mem_normalizer_iff.mp (hD_norm (hKD ha)) n).mp hn) hd
  have hfk : f * k = k * f := (h6 k hk f (sixH_h16_Cstar_le_Mhat hS hf)).symm
  have hkf : k⁻¹ * f⁻¹ = f⁻¹ * k⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hfk]
  have hc₀M : f⁻¹ * m⁻¹ * f * m ∈ Mhat φ t i i :=
    (Mhat φ t i i).mul_mem ((Subgroup.mem_normalizer_iff''.mp hfN m⁻¹).mp
      ((Mhat φ t i i).inv_mem hm)) hm
  have hc₀C : f⁻¹ * m⁻¹ * f * m ∈ Cstar φ t i := by
    have := (Cstar φ t i).mul_mem ((Cstar φ t i).inv_mem hf)
      (sixH_h16_Cstar_conj hS hM2 (hMT ((Mhat φ t i i).inv_mem hm)) hf)
    simpa [mul_assoc] using this
  have hc₀ : f⁻¹ * m⁻¹ * f * m ∈ Mc φ t i := by
    rw [← h8.1]
    exact mem_inf.mpr ⟨hc₀M, SixG.Cstar_le_P₂ hS.fc i hS.ne_bot hS.eq_bot hc₀C⟩
  have e : f⁻¹ * (m * k)⁻¹ * f * (m * k) = k⁻¹ * (f⁻¹ * m⁻¹ * f * m) * k :=
    calc f⁻¹ * (m * k)⁻¹ * f * (m * k) = (f⁻¹ * k⁻¹) * (m⁻¹ * f * m) * k := by group
      _ = (k⁻¹ * f⁻¹) * (m⁻¹ * f * m) * k := by rw [hkf]
      _ = k⁻¹ * (f⁻¹ * m⁻¹ * f * m) * k := by group
  rw [e]
  have := sixH_h16_M_conj h9 (inv_mem (hKT hk)) hc₀
  simpa using this

open scoped Pointwise in
theorem sixH_h16_F_decomp (h : FullCenter.FCHyp L K n φ t) (i : Axis) {y : G} (hy : y ∈ F φ t) :
    ∃ a ∈ Wk φ t i, ∃ b ∈ Wk φ t i.swap, y = a * b := by
  have hy' : y ∈ ((Wk φ t Axis.one : Subgroup G) : Set G) *
      ((Wk φ t Axis.two : Subgroup G) : Set G) := by
    rw [FullCenterTorus.W_mul_W h]
    exact hy
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := Set.mem_mul.1 hy'
  cases i
  · exact ⟨a₁, ha₁, b₁, hb₁, rfl⟩
  · exact ⟨b₁, hb₁, a₁, ha₁, FullCenterTorus.F_comm h (FullCenterTorus.W_le_F _ ha₁)
      (FullCenterTorus.W_le_F _ hb₁)⟩

theorem sixH_h16_W_sq_eq (hS : SCSetting L K n φ t i) {w' : G} (hw : w' ∈ Wk φ t i) :
    w' * w' = t⁻¹ * (w'⁻¹ * t * w') := by
  have hk := FullCenterTorus.kappa_mem_U hS.fc i (FullCenterTorus.W_le_Fi hS.fc i hw).2
  obtain ⟨a, ha⟩ := RootAxisTwoCore.exists_coordG_eq φ i hk
  exact (SingleComm.W_sq_eq hS.fc i hS.ne_bot hS.eq_bot hw ha.symm).trans ha

theorem sixH_h16_W_sq_one (hS : SCSetting L K n φ t i) {a : G} (ha : a ∈ Wk φ t i)
    (haa : a * a = 1) : a ∈ U φ i := by
  have h1 : t⁻¹ * (a⁻¹ * t * a) = 1 := (sixH_h16_W_sq_eq hS ha).symm.trans haa
  have h2 : t = a⁻¹ * t * a := inv_mul_eq_one.mp h1
  have h3 : a * t = t * a :=
    calc a * t = a * (a⁻¹ * t * a) := by rw [← h2]
      _ = t * a := by group
  have hmem : a ∈ Wk φ t i ⊓ centralizer ({t} : Set G) :=
    mem_inf.mpr ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr h3⟩
  rwa [FullCenterTorus.W_inf_C hS.fc i] at hmem

theorem sixH_h16_Fw_sq (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    {f : G} (hf : f ∈ Fw φ t i.swap) (hff : f * f ∈ Mc φ t i) : f ∈ Dstar φ t i := by
  have h2b := sixH_h2b hS hM2
  have hFM : F φ t ≤ Mc φ t i := NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot
  have hMD : Mc φ t i ≤ Dstar φ t i := le_sup_left.trans le_sup_left
  have hf₂ : w φ i.swap * f * (w φ i.swap)⁻¹ ∈ F φ t := FullCenterWeyl.mem_map_conj_inv.mp hf
  obtain ⟨a, ha, b, hb, hab⟩ := sixH_h16_F_decomp hS.fc i hf₂
  have hf_eq : f = (w φ i.swap)⁻¹ * (a * b) * w φ i.swap := by
    rw [← hab]
    group
  have hbb : b * b = 1 := SingleComm.sq_W_swap hS.fc i hS.ne_bot hS.eq_bot hb
  have hba : b * a = a * b :=
    FullCenterTorus.F_comm hS.fc (FullCenterTorus.W_le_F _ hb) (FullCenterTorus.W_le_F _ ha)
  have hab2 : (a * b) * (a * b) = a * a :=
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hba]
      _ = (a * a) * (b * b) := by group
      _ = a * a := by rw [hbb, mul_one]
  have hff' : f * f = (w φ i.swap)⁻¹ * (a * a) * w φ i.swap := by
    calc f * f = (w φ i.swap)⁻¹ * ((a * b) * (a * b)) * w φ i.swap := by
          conv_lhs => rw [hf_eq]
          group
      _ = _ := by rw [hab2]
  have hu : a * a ∈ U φ i := SingleComm.W_sq_mem_U hS.fc i ha
  have hu' : a * a ∈ U φ i.swap.swap := by
    rw [sixH_h14_swap_swap]
    exact hu
  have hu1 : a * a = 1 := by
    by_contra hne
    obtain ⟨hA, hZ⟩ := (sixH_s2_weyl i.swap).2 (a * a) hu' hne
    have hmem : (w φ i.swap)⁻¹ * (a * a) * w φ i.swap ∈ Mc φ t i ⊓ centralizer ({t} : Set G) :=
      mem_inf.mpr ⟨hff' ▸ hff, FullCenterWeyl.A_le_C hS.fc i.swap hA⟩
    exact hZ ((NextCores.M_inf_C hS.fc i hS.ne_bot hS.eq_bot).le hmem)
  have haU : a ∈ U φ i := sixH_h16_W_sq_one hS ha hu1
  have haU' : a ∈ U φ i.swap.swap := by
    rw [sixH_h14_swap_swap]
    exact haU
  have hag : (w φ i.swap)⁻¹ * a * w φ i.swap ∈ Dstar φ t i := by
    by_cases ha1 : a = 1
    · rw [ha1, mul_one, inv_mul_cancel]
      exact one_mem _
    · exact (le_sup_right : Kc φ t i.swap ≤ Dstar φ t i)
        ((le_sup_left : A φ i.swap ≤ Kc φ t i.swap) ((sixH_s2_weyl i.swap).2 a haU' ha1).1)
  have hbV : b ∈ Vtor φ t i i.swap := (RootStandard.V_swap_eq hS.fc i hS.ne_bot hS.eq_bot).ge hb
  have hbg : (w φ i.swap)⁻¹ * b * w φ i.swap ∈ Dstar φ t i :=
    hMD (hFM (FullCenterTorus.W_le_F _
      ((RootStandard.V_swap_eq hS.fc i hS.ne_bot hS.eq_bot).le (h2b.2 b hbV))))
  have e : f = ((w φ i.swap)⁻¹ * a * w φ i.swap) * ((w φ i.swap)⁻¹ * b * w φ i.swap) := by
    conv_lhs => rw [hf_eq]
    group
  rw [e]
  exact (Dstar φ t i).mul_mem hag hbg

theorem sixH_h16_crit (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h3 : H3Concl φ t i) (h4a : H4aConcl φ t i) (h6 : H6Concl φ t i) (h8 : H8Concl φ t i)
    (h9 : H9Concl φ t i) (h11 : H11Concl φ t i)
    (hCN : ∀ g ∈ Cstar φ t i, g ∈ normalizer (Mhat φ t i i : Set G)) {x : G}
    (hxT : x ∈ Tbar φ t i) (hxS : x ∈ S φ t i) (hxx : x * x ∈ Mc φ t i) :
    x ∈ Dstar φ t i := by
  obtain ⟨d, hd, f, hf, rfl⟩ := sixH_h16_omega hS hM2 h4a h8 h11 hxT hxS
  have hfC : f ∈ Cstar φ t i := (le_sup_right : Fw φ t i.swap ≤ Cstar φ t i) hf
  have hcomm := sixH_h16_comm hS hM2 h6 h8 h9 h11 hfC (hCN f hfC) hd
  have hfT : f ∈ Tplus φ t i := sixH_h16_Cstar_le_Tplus hS hfC
  have hcM : f⁻¹ * (f⁻¹ * d⁻¹ * f * d) * f ∈ Mc φ t i := by
    have := sixH_h16_M_conj h9 (inv_mem hfT) hcomm
    rwa [inv_inv] at this
  have hf2 : f * f ∈ Mc φ t i := by
    have e : f ^ 2 = (d * d)⁻¹ * ((d * f) * (d * f)) * (f⁻¹ * (f⁻¹ * d⁻¹ * f * d) * f)⁻¹ := by
      group
    rw [← sq, e]
    exact (Mc φ t i).mul_mem ((Mc φ t i).mul_mem
      ((Mc φ t i).inv_mem (sixH_h16_D_sq hS hM2 h3 h11 hd)) hxx) ((Mc φ t i).inv_mem hcM)
  exact (Dstar φ t i).mul_mem hd (sixH_h16_Fw_sq hS hM2 hf hf2)

theorem sixH_h16_Cstar_normalizes (hS : SCSetting L K n φ t i)
    (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i) (h1 : H1Concl φ t i) (h3 : H3Concl φ t i)
    (h8 : H8Concl φ t i) (h9 : H9Concl φ t i) (h11 : H11Concl φ t i) (h13 : H13Concl φ t i) :
    ∀ g ∈ Cstar φ t i, g ∈ normalizer (Mhat φ t i i : Set G) := by
  intro g hg
  have hgTbar : g ∈ Tbar φ t i :=
    (le_sup_right : T₂ φ t i.swap ≤ Tbar φ t i)
      ((SixG.Astar_le_T₂ hS.fc i hS.ne_bot hS.eq_bot) ((SixG.Cstar_le_Astar i) hg))
  exact sixH_h16_uniq hS hM2 h1 h3 h9 h11 h13 (sixH_h16_Cstar_le_Tplus hS hg)
    (sixH_h16_Tbar_normalizes_D hS h8 h11 hgTbar)

theorem sixH_h16_T₀_normalizes (hS : SCSetting L K n φ t i)
    (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i) (h1 : H1Concl φ t i) (h3 : H3Concl φ t i)
    (h4a : H4aConcl φ t i) (h6 : H6Concl φ t i) (h8 : H8Concl φ t i) (h9 : H9Concl φ t i)
    (h11 : H11Concl φ t i) (h13 : H13Concl φ t i) :
    T₀ φ t i.swap ≤ normalizer (Dstar φ t i : Set G) := by
  have hCN := sixH_h16_Cstar_normalizes hS hM2 h1 h3 h8 h9 h11 h13
  have hUM := sixH_h13_U_le_Mc hS hM2
  have hUc := sixH_U_comm_Tplus h1
  have hD_norm : Dstar φ t i ≤ normalizer (Mhat φ t i i : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp h11.2.2.2.1
  have hKD : Kc φ t i.swap ≤ Dstar φ t i := le_sup_right
  have hDS : Dstar φ t i ≤ S φ t i := by
    rw [h11.2.2.2.2]
    exact inf_le_right
  have hDT : Dstar φ t i ≤ Tbar φ t i := by
    rw [h11.2.2.2.2]
    exact inf_le_left.trans le_sup_left
  intro g hg
  have hgT : g ∈ Tplus φ t i := (le_sup_right : T₀ φ t i.swap ≤ Tplus φ t i) hg
  have hTbarN := SixG.T₀_le_normalizer_Tbar hS.fc i hS.ne_bot hS.eq_bot hM2 hg
  have hSN := sixH_h16_Tplus_normalizes_S h8 hgT
  refine RootAxisTwoCore.mem_normalizer_of_conj_le fun q hq => ?_
  obtain ⟨m, hm, k, hk, rfl⟩ := sixH_g8_mem_sup_mul (N := Mhat φ t i i) (A := Kc φ t i.swap)
    (fun a ha n hn => (Subgroup.mem_normalizer_iff.mp (hD_norm (hKD ha)) n).mp hn) hq
  have hmD : m ∈ Dstar φ t i := (le_sup_left : Mhat φ t i i ≤ Dstar φ t i) hm
  have hxD : g * m * g⁻¹ ∈ Dstar φ t i := by
    refine sixH_h16_crit hS hM2 h3 h4a h6 h8 h9 h11 hCN
      ((Subgroup.mem_normalizer_iff.mp hTbarN m).mp (hDT hmD))
      ((Subgroup.mem_normalizer_iff.mp hSN m).mp (hDS hmD)) ?_
    have hsq : m * m ∈ U φ i := by
      have : m * m ∈ closure {x : G | ∃ y ∈ Mhat φ t i i, x = y * y} :=
        subset_closure ⟨m, hm, rfl⟩
      rwa [h3.2] at this
    have e : g * m * g⁻¹ * (g * m * g⁻¹) = g * (m * m) * g⁻¹ := by group
    rw [e, hUc _ hsq g hgT, mul_inv_cancel_right]
    exact hUM hsq
  have hkD : g * k * g⁻¹ ∈ Dstar φ t i := hKD (sixH_h16_Kj_conj hS hM2 hgT hk)
  have e : g * (m * k) * g⁻¹ = (g * m * g⁻¹) * (g * k * g⁻¹) := by group
  rw [e]
  exact (Dstar φ t i).mul_mem hxD hkD

theorem sixH_h16 (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1 : H1Concl φ t i) (h3 : H3Concl φ t i) (h8 : H8Concl φ t i) (h9 : H9Concl φ t i)
    (h11 : H11Concl φ t i) (h13 : H13Concl φ t i) :
    SixG.MNNormalIn (Dstar φ t i) (Tplus φ t i) (J₀ φ) ∧
      SixG.MNNormalIn (Mhat φ t i i) (Tplus φ t i) (J₀ φ) := by
  have h2b := sixH_h2b hS hM2
  have h4a := sixH_h4a hS hM2 h1 h3
  have h6 := sixH_h6 hS hM2 h1 h2b (sixH_h5 hS hM2)
  have hTbarN := sixH_h16_Tbar_normalizes_D hS h8 h11
  have hTD : Tplus φ t i ≤ normalizer (Dstar φ t i : Set G) :=
    sup_le hTbarN (sixH_h16_T₀_normalizes hS hM2 h1 h3 h4a h6 h8 h9 h11 h13)
  have hTM : Tplus φ t i ≤ normalizer (Mhat φ t i i : Set G) := fun g hg =>
    sixH_h16_uniq hS hM2 h1 h3 h9 h11 h13 hg (hTD hg)
  have hDT : Dstar φ t i ≤ Tplus φ t i := by
    rw [h11.2.2.2.2]
    exact inf_le_left.trans (le_sup_left.trans le_sup_left)
  have hJM : J₀ φ ≤ normalizer (Mhat φ t i i : Set G) :=
    SixF.J_le_normalizer_Mhat hS.fc i hS.ne_bot hS.eq_bot
  have hJK : J₀ φ ≤ normalizer (Kc φ t i.swap : Set G) := SixG.J_le_normalizer_K hS.fc i.swap
  refine ⟨⟨hDT, (Subgroup.normal_subgroupOf_iff_le_normalizer hDT).mpr hTD, ?_⟩,
    ⟨sixH_h16_Mhat_le_Tplus hS,
      (Subgroup.normal_subgroupOf_iff_le_normalizer (sixH_h16_Mhat_le_Tplus hS)).mpr hTM, hJM⟩⟩
  intro j hj
  refine RootAxisTwoCore.mem_normalizer_of_conj_le fun q hq =>
    RootAxisTwoCore.conj_mem_sup (H₁ := Mhat φ t i i) (H₂ := Kc φ t i.swap)
      (fun x hx => (Subgroup.mem_normalizer_iff.mp (hJM hj) x).mp hx)
      (fun x hx => (Subgroup.mem_normalizer_iff.mp (hJK hj) x).mp hx) hq

end Steps

section Assembly

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixH_of_steps (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i) :
    SixHConclusion φ t i := by
  have h1a := sixH_h1a_normalizer_A hS hM2
  have h1 := sixH_h1_center_Tplus hS hM2 h1a
  have h2a := sixH_h2a hS hM2 h1
  have h2b := sixH_h2b hS hM2
  have h2c := sixH_h2c hS hM2 h1 h2a
  have h2d := sixH_h2d hS hM2 h1 h2a h2c
  have h3 := sixH_h3 hS hM2 h1 h2a h2b
  have h4a := sixH_h4a hS hM2 h1 h3
  have h4 := sixH_h4 hS hM2 h1 h3 h4a
  have h5 := sixH_h5 hS hM2
  have h6 := sixH_h6 hS hM2 h1 h2b h5
  have h7 := sixH_h7 hS hM2 h1 h5 h6
  have h8 := sixH_h8 hS hM2 h7
  have h9 := sixH_h9 hS hM2 h1 h2a h3 h6
  have h10 := sixH_h10 hS hM2 h1a h1 h2a h2d h6 h7 h9
  have h11 := sixH_h11 hS hM2 h4 h6 h8
  have h12 := sixH_h12 hS hM2 h3 h4 h6
  have h13 := sixH_h13 hS hM2 h3 h4 h6 h11 h12
  have h14 := sixH_h14 hS hM2 h1 h2d h3 h4a
  have h15 := sixH_h15 hS hM2 h1 h11 h12 h14
  have h16 := sixH_h16 hS hM2 h1 h3 h8 h9 h11 h13
  obtain ⟨h8a, h8b, h8c, h8d, h8e, -⟩ := h8
  exact ⟨h3.2, h14, h10.2, h10.1, fun k => by
      rcases SingleComm.eq_or_eq_swap i k with rfl | rfl
      · exact h16.2
      · exact h7.2, h9, h16.1, h15, h11.2.2.1, h11.1, h13, h4.1, h8b, h8c, h8d, h8e, h1,
    SixG.isPGroup_Tplus hS.fc i hS.ne_bot hS.eq_bot hM2⟩

theorem sixH
    (hSel : CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootSelector fun D _ => CFSG.Blueprint.Catalog D) :
    SixHStatement := by
  intro G _ _ _ L K _ _ _ n φ t i hS
  exact sixH_of_steps hS (scsetting_sq_M_mem_U hSel hS)

end Assembly

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
