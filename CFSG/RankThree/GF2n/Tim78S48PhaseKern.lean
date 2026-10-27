module

public import CFSG.RankThree.GF2n.Tim78S48PhaseSwap
public import CFSG.RankThree.GF2n.Tim78S48PhaseWeyl
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.RankThree.GF2n.Tim78Frattini

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open Matrix
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

section Cert43


theorem Tg_comm_mem_Bg {t₁ t₂ : G} (h₁ : t₁ ∈ conjSubgroup g T) (h₂ : t₂ ∈ conjSubgroup g T) :
    ⁅t₁, t₂⁆ ∈ conjSubgroup g B := by
  have hT2 : IsPGroup 2 T := H.isPGroup_Q.to_le H.T_le_Q
  have hfr : inSubgroup frattini T = B :=
    H.frattini_eq_B_of_ne H.B_le_T H.T_le_Q H.M_le_normalizer_T H.B_ne_T
  rw [mem_conjSubgroup] at h₁ h₂ ⊢
  have h := commutatorElement_mem_inSubgroup_frattini hT2 h₁ h₂
  rw [hfr] at h
  have e : g⁻¹ * ⁅t₁, t₂⁆ * g = ⁅g⁻¹ * t₁ * g, g⁻¹ * t₂ * g⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact h

theorem kdata (h48 : Hyp48 M B T g) (hKe : Assembly.IsElemAbelian 2 (kernel48 B T g)) :
    KData B (conjSubgroup g B) T (conjSubgroup g T) (kernel48 B T g) := by
  have hT2 : IsPGroup 2 T := H.isPGroup_Q.to_le H.T_le_Q
  have hfr : inSubgroup frattini T = B :=
    H.frattini_eq_B_of_ne H.B_le_T H.T_le_Q H.M_le_normalizer_T H.B_ne_T
  have hWK := H.W_le_kernel h48
  have hXK := H.X_le_normalizer_kernel h48
  refine ⟨fun a ha b hb => comm_of_isElemAbelian hKe ha hb,
    fun a ha => CFSG.Open.IsElemAbelian.mul_self_eq_one hKe ha,
    le_inf H.B_le_T ((le_sup_left : B ≤ B ⊔ conjSubgroup g B).trans hWK),
    le_inf (conjSubgroup_mono_of_le H.B_le_T)
      ((le_sup_right : conjSubgroup g B ≤ B ⊔ conjSubgroup g B).trans hWK), ?_, ?_, ?_,
    fun t ht b hb => H.T_comm_B ht hb, ?_, ?_, ?_⟩
  · intro t ht k hk
    have h1 : k * t⁻¹ * k⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (H.kernel_le_normalizer_T hk) t⁻¹).mp (T.inv_mem ht)
    have h2 : t * k * t⁻¹ ∈ kernel48 B T g :=
      (Subgroup.mem_normalizer_iff.mp (hXK (Subgroup.mem_sup_left ht)) k).mp hk
    refine ⟨?_, ?_⟩
    · have : ⁅t, k⁆ = t * (k * t⁻¹ * k⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]; exact T.mul_mem ht h1
    · have : ⁅t, k⁆ = (t * k * t⁻¹) * k⁻¹ := by simp [commutatorElement_def]
      rw [this]; exact (kernel48 B T g).mul_mem h2 ((kernel48 B T g).inv_mem hk)
  · intro t ht k hk
    have h1 : k * t⁻¹ * k⁻¹ ∈ conjSubgroup g T :=
      (Subgroup.mem_normalizer_iff.mp (H.kernel_le_normalizer_Tg hk) t⁻¹).mp
        ((conjSubgroup g T).inv_mem ht)
    have h2 : t * k * t⁻¹ ∈ kernel48 B T g :=
      (Subgroup.mem_normalizer_iff.mp (hXK (Subgroup.mem_sup_right ht)) k).mp hk
    refine ⟨?_, ?_⟩
    · have : ⁅t, k⁆ = t * (k * t⁻¹ * k⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]; exact (conjSubgroup g T).mul_mem ht h1
    · have : ⁅t, k⁆ = (t * k * t⁻¹) * k⁻¹ := by simp [commutatorElement_def]
      rw [this]; exact (kernel48 B T g).mul_mem h2 ((kernel48 B T g).inv_mem hk)
  · intro t ht x hx
    rw [← hfr]
    exact commutatorElement_mem_inSubgroup_frattini hT2 ht hx.1
  · intro t ht b hb
    rw [← commutatorElement_inv]
    exact B.inv_mem (h48.comm_T b hb t ht)
  · intro t ht b hb
    rw [← commutatorElement_inv]
    exact (conjSubgroup g B).inv_mem (h48.comm_Tg b hb t ht)
  · intro t ht
    rw [← hfr, ← pow_two]
    exact sq_mem_inSubgroup_frattini hT2 ht

theorem T0_eq (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) (C : Core48 Q B T g)
    {f : ℕ} (hf : 2 ≤ f) (D : L2Coords B T g (GaloisField 2 f))
    {Θ : (Fin 2 → GaloisField 2 f) → G} (N : IsNatCoords D Θ) {K₁ : Subgroup G}
    (hK₁ : IsTorusLift D K₁) (hT₀e : Assembly.IsElemAbelian 2 (T ⊓ kernel48 B T g))
    (hrel : (T ⊓ kernel48 B T g).relIndex T = 2 ^ f) (hlt : B < T ⊓ kernel48 B T g) :
    T ⊓ kernel48 B T g = B ⊔ (T ⊓ conjSubgroup g T) := by
  classical
  have hf0 : f ≠ 0 := by omega
  have hTK := C.exists_T_not_kernel
  have hTgK := C.exists_Tg_not_kernel
  have hXK := H.X_le_normalizer_kernel h48
  have hkd := H.kdata h48 C.phase.1
  choose u hu hεu using fun s : GaloisField 2 f => D.exists_T s
  choose v hv hεv using fun s : GaloisField 2 f => D.exists_Tg s⁻¹
  have hsw : ∀ s : GaloisField 2 f, s ≠ 0 → WeylSwap B T g (u s * v s * u s) := fun s hs =>
    H.weyl_swap h48 hP C N hs (hu s) (hv s) (hεu s) (hεv s)
  have hw : ∀ s : GaloisField 2 f, s ≠ 0 → ∀ x ∈ T ⊓ kernel48 B T g,
      (u s * v s * u s) * x * (u s * v s * u s)⁻¹ ∈ conjSubgroup g T ⊓ kernel48 B T g := by
    intro s hs x hx
    have W₀ := hsw s hs
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hXK W₀.mem_X) x).mp hx.2⟩
    have := mul_mul_inv_mem_conjSubgroup (u s * v s * u s) hx.1
    rwa [W₀.conj_T] at this
  have hadd : ∀ s s' : GaloisField 2 f, ∃ κ ∈ T ⊓ kernel48 B T g,
      u (s + s') = u s * u s' * κ := by
    intro s s'
    have h1 := inv_mul_mem_T_kernel D (T.mul_mem (hu s) (hu s')) (hu (s + s')) (by
      have e : (⟨u s * u s', Subgroup.mem_sup_left (T.mul_mem (hu s) (hu s'))⟩ :
          ↥(T ⊔ conjSubgroup g T)) = ⟨u s, Subgroup.mem_sup_left (hu s)⟩ *
            ⟨u s', Subgroup.mem_sup_left (hu s')⟩ := rfl
      rw [e, map_mul, hεu, hεu, hεu, utriElt_add])
    exact ⟨_, h1, by group⟩
  have hgen : ∀ t ∈ T, ∃ s, ∃ κ ∈ T ⊓ kernel48 B T g, t = u s * κ := by
    intro t ht
    obtain ⟨s, hs⟩ := D.exists_utri ht
    have h1 := inv_mul_mem_T_kernel D (hu s) ht (by rw [hεu s, hs])
    exact ⟨s, _, h1, by group⟩
  have hS : B ⊔ (T ⊓ conjSubgroup g T) ≤ T ⊓ kernel48 B T g :=
    sup_le hkd.B_le fun a ha => ⟨ha.1, inf_Tg_le_kernel D ha⟩
  have hw1 := hsw 1 one_ne_zero
  have hcard : (conjSubgroup g B ⊔ (T ⊓ conjSubgroup g T)).relIndex
      (conjSubgroup g T ⊓ kernel48 B T g) =
      (B ⊔ (T ⊓ conjSubgroup g T)).relIndex (T ⊓ kernel48 B T g) := by
    rw [← hw1.conj_S, ← H.conj_T0 h48 hw1, relIndex_conjSubgroup]
  have hm : B.relIndex (T ⊓ kernel48 B T g) ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f hf0]
    exact H.T0_relIndex_le h48 hP hTK hTgK hf0 D hK₁ hT₀e hrel
  have hZ : ∀ x ∈ T, (∀ t ∈ T, x * t = t * x) → x ∈ B := by
    intro x hx hc
    have : x ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
      ⟨hx, Subgroup.mem_centralizer_iff.mpr fun t ht => (hc t ht).symm⟩
    rwa [H.inf_centralizer_eq_B H.B_le_T H.T_le_Q H.M_le_normalizer_T] at this
  have hBTg : B ⊓ conjSubgroup g T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) :=
      ⟨hx.2, Subgroup.mem_sup_left hx.1⟩
    rw [C.Tg_inf_W] at h1
    have h2 : x ∈ B ⊓ conjSubgroup g B := ⟨hx.1, h1⟩
    rwa [H.B_inf_Bg hP] at h2
  exact le_antisymm (hkd.T0_le_sup (fun s => CharTwo.add_self_eq_zero s) u v hu hv hadd hgen hw
    hS hcard hm hZ hBTg hlt) hS

theorem kernel_eq (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) (C : Core48 Q B T g)
    {f : ℕ} (hf : 2 ≤ f) (D : L2Coords B T g (GaloisField 2 f))
    {Θ : (Fin 2 → GaloisField 2 f) → G} (N : IsNatCoords D Θ) {K₁ : Subgroup G}
    (hK₁ : IsTorusLift D K₁) (hT₀e : Assembly.IsElemAbelian 2 (T ⊓ kernel48 B T g))
    (hrel : (T ⊓ kernel48 B T g).relIndex T = 2 ^ f) (hlt : B < T ⊓ kernel48 B T g) :
    kernel48 B T g = (B ⊔ conjSubgroup g B) ⊔ (T ⊓ conjSubgroup g T) := by
  have hT0 := H.T0_eq h48 hP C hf D N hK₁ hT₀e hrel hlt
  obtain ⟨w, hw⟩ := H.exists_weyl h48 hP C N
  have hT0' : conjSubgroup g T ⊓ kernel48 B T g = conjSubgroup g B ⊔ (T ⊓ conjSubgroup g T) := by
    rw [← H.conj_T0 h48 hw, hT0, hw.conj_S]
  calc kernel48 B T g
      = (T ⊓ kernel48 B T g) ⊔ (conjSubgroup g T ⊓ kernel48 B T g) := C.phase.2.1
    _ = (B ⊔ (T ⊓ conjSubgroup g T)) ⊔ (conjSubgroup g B ⊔ (T ⊓ conjSubgroup g T)) := by
        rw [hT0', hT0]
    _ = (B ⊔ conjSubgroup g B) ⊔ (T ⊓ conjSubgroup g T) := by
        rw [sup_sup_sup_comm, sup_idem]

theorem W_inf_A (hP : ¬ conjSubgroup g B ≤ P) (C : Core48 Q B T g) :
    (B ⊔ conjSubgroup g B) ⊓ (T ⊓ conjSubgroup g T) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ T ⊓ (B ⊔ conjSubgroup g B) := ⟨hx.2.1, hx.1⟩
  have h2 : x ∈ conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) := ⟨hx.2.2, hx.1⟩
  rw [C.T_inf_W] at h1
  rw [C.Tg_inf_W] at h2
  have h3 : x ∈ B ⊓ conjSubgroup g B := ⟨h1, h2⟩
  rwa [H.B_inf_Bg hP] at h3

theorem comm_X_kernel (h48 : Hyp48 M B T g)
    (hKA : kernel48 B T g = (B ⊔ conjSubgroup g B) ⊔ (T ⊓ conjSubgroup g T)) :
    ∀ h ∈ T ⊔ conjSubgroup g T, ∀ k ∈ kernel48 B T g, ⁅h, k⁆ ∈ B ⊔ conjSubgroup g B := by
  have hT2 : IsPGroup 2 T := H.isPGroup_Q.to_le H.T_le_Q
  have hfr : inSubgroup frattini T = B :=
    H.frattini_eq_B_of_ne H.B_le_T H.T_le_Q H.M_le_normalizer_T H.B_ne_T
  have hX : T ⊔ conjSubgroup g T ≤ commSub (B ⊔ conjSubgroup g B) (T ⊓ conjSubgroup g T) :=
    sup_le (fun t ht => mem_commSub.mpr ⟨H.T_le_normalizer_W h48 ht, fun a ha =>
      Subgroup.mem_sup_left (hfr ▸ commutatorElement_mem_inSubgroup_frattini hT2 ht ha.1)⟩)
      (fun t ht => mem_commSub.mpr ⟨H.Tg_le_normalizer_W h48 ht, fun a ha =>
        Subgroup.mem_sup_right (H.Tg_comm_mem_Bg ht ha.2)⟩)
  intro h hh k hk
  have hh' := mem_commSub.mp (hX hh)
  have hAK : T ⊓ conjSubgroup g T ≤ kernel48 B T g := by rw [hKA]; exact le_sup_right
  rw [hKA] at hk
  obtain ⟨w', hw', a', ha', rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.mp (hAK hx).2 y hy).symm) hk
  have e : ⁅h, w' * a'⁆ = (h * w' * h⁻¹ * w'⁻¹) * w' * ⁅h, a'⁆ * w'⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  have h1 : h * w' * h⁻¹ ∈ B ⊔ conjSubgroup g B :=
    (Subgroup.mem_normalizer_iff.mp hh'.1 w').mp hw'
  have h2 : h * w' * h⁻¹ * w'⁻¹ ∈ B ⊔ conjSubgroup g B :=
    (B ⊔ conjSubgroup g B).mul_mem h1 ((B ⊔ conjSubgroup g B).inv_mem hw')
  exact (B ⊔ conjSubgroup g B).mul_mem ((B ⊔ conjSubgroup g B).mul_mem
    ((B ⊔ conjSubgroup g B).mul_mem h2 hw') (hh'.2 a' ha')) ((B ⊔ conjSubgroup g B).inv_mem hw')

theorem K₁_le_centralizer (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (C : Core48 Q B T g) {F : Type} [Field F] (D : L2Coords B T g F) {K₁ : Subgroup G}
    (hK₁ : IsTorusLift D K₁)
    (hcomm : ∀ h ∈ T ⊔ conjSubgroup g T, ∀ k ∈ kernel48 B T g, ⁅h, k⁆ ∈ B ⊔ conjSubgroup g B)
    (hWA : (B ⊔ conjSubgroup g B) ⊓ (T ⊓ conjSubgroup g T) = ⊥) :
    K₁ ≤ Subgroup.centralizer ((T ⊓ conjSubgroup g T : Subgroup G) : Set G) := by
  have hTK := C.exists_T_not_kernel
  have hTgK := C.exists_Tg_not_kernel
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hkX : k ∈ T ⊔ conjSubgroup g T := hK₁.le_X hk
  have hn := H.torus_normalizes h48 hP hTK hTgK D (x := ⟨k, hkX⟩) (hK₁.eps_mem ⟨k, hkX⟩ hk)
  have hkT : k ∈ Subgroup.normalizer (T : Set G) :=
    H.M_le_normalizer_T (by rw [← H.normalizer_B]; exact hn.1)
  have hkTg : k ∈ Subgroup.normalizer (conjSubgroup g T : Set G) :=
    normalizer_conj_le g (by rw [H.normalizer_B]; exact H.M_le_normalizer_T) hn.2
  have hAK : a ∈ kernel48 B T g := inf_Tg_le_kernel D ha
  have h1 : ⁅k, a⁆ ∈ B ⊔ conjSubgroup g B := hcomm k hkX a hAK
  have h2 : ⁅k, a⁆ ∈ T ⊓ conjSubgroup g T := by
    have e : ⁅k, a⁆ = (k * a * k⁻¹) * a⁻¹ := by simp [commutatorElement_def]
    rw [e]
    exact (T ⊓ conjSubgroup g T).mul_mem
      ⟨(Subgroup.mem_normalizer_iff.mp hkT a).mp ha.1,
        (Subgroup.mem_normalizer_iff.mp hkTg a).mp ha.2⟩ ((T ⊓ conjSubgroup g T).inv_mem ha)
  have h3 : ⁅k, a⁆ ∈ (B ⊔ conjSubgroup g B) ⊓ (T ⊓ conjSubgroup g T) := ⟨h1, h2⟩
  rw [hWA, Subgroup.mem_bot] at h3
  have h4 : k * a * k⁻¹ * a⁻¹ = 1 := h3
  calc a * k = (k * a * k⁻¹ * a⁻¹) * (a * k) * 1 := by rw [h4]; group
    _ = k * a := by group

theorem kernel_structure (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (C : Core48 Q B T g) {f : ℕ} (hf : 2 ≤ f) (D : L2Coords B T g (GaloisField 2 f))
    {Θ : (Fin 2 → GaloisField 2 f) → G} (N : IsNatCoords D Θ) {K₁ : Subgroup G}
    (hK₁ : IsTorusLift D K₁) (hT₀e : Assembly.IsElemAbelian 2 (T ⊓ kernel48 B T g))
    (hrel : (T ⊓ kernel48 B T g).relIndex T = 2 ^ f) (hlt : B < T ⊓ kernel48 B T g) :
    kernel48 B T g = (B ⊔ conjSubgroup g B) ⊔ (T ⊓ conjSubgroup g T) ∧
    (B ⊔ conjSubgroup g B) ⊓ (T ⊓ conjSubgroup g T) = ⊥ ∧ T ⊓ conjSubgroup g T ≠ ⊥ ∧
    (∀ h ∈ T ⊔ conjSubgroup g T, ∀ k ∈ kernel48 B T g, ⁅h, k⁆ ∈ B ⊔ conjSubgroup g B) ∧
    K₁ ≤ Subgroup.centralizer ((T ⊓ conjSubgroup g T : Subgroup G) : Set G) := by
  have hKA := H.kernel_eq h48 hP C hf D N hK₁ hT₀e hrel hlt
  have hWA := H.W_inf_A hP C
  have hcomm := H.comm_X_kernel h48 hKA
  refine ⟨hKA, hWA, ?_, hcomm, H.K₁_le_centralizer h48 hP C D hK₁ hcomm hWA⟩
  intro hbot
  have hT0 := H.T0_eq h48 hP C hf D N hK₁ hT₀e hrel hlt
  rw [hbot, sup_bot_eq] at hT0
  exact hlt.ne hT0.symm

end Cert43

end Hyp4

end CFSG.RankThree.GF2n.Tim78
