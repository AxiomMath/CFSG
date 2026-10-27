module

public import CFSG.Quasithin.Vol2.Ch11SecAKA18

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.Open (pCoreOf)

namespace KA

variable {K : Type} [Field K]

theorem eq_basis (v : Fin 2 ⊕ Fin 2 → K) :
    v = v (.inl 0) • vec4 1 0 0 0 + v (.inl 1) • vec4 0 1 0 0 + v (.inr 0) • vec4 0 0 1 0 +
      v (.inr 1) • vec4 0 0 0 1 :=
  vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4]) (by simp [vec4])

theorem shape_inr {T : (Fin 2 ⊕ Fin 2 → K) → (Fin 2 ⊕ Fin 2 → K)}
    (hadd : ∀ x y, T (x + y) = T x + T y) (hsmul : ∀ (c : K) x, T (c • x) = c • T x)
    {μ ν : K} (h0 : T (vec4 1 0 0 0) = μ • vec4 1 0 0 0)
    (h1 : T (vec4 0 1 0 0) = μ • vec4 0 1 0 0) (h2 : T (vec4 0 0 1 0) (.inr 0) = ν)
    (h3 : T (vec4 0 0 1 0) (.inr 1) = 0) (h4 : T (vec4 0 0 0 1) (.inr 0) = 0)
    (h5 : T (vec4 0 0 0 1) (.inr 1) = ν) (v : Fin 2 ⊕ Fin 2 → K) :
    T v (.inr 0) = ν * v (.inr 0) ∧ T v (.inr 1) = ν * v (.inr 1) := by
  have hv : T v = v (.inl 0) • (μ • vec4 1 0 0 0) + v (.inl 1) • (μ • vec4 0 1 0 0) +
      v (.inr 0) • T (vec4 0 0 1 0) + v (.inr 1) • T (vec4 0 0 0 1) := by
    conv_lhs => rw [eq_basis v]
    rw [hadd, hadd, hadd, hsmul, hsmul, hsmul, hsmul, h0, h1]
  rw [hv]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec4_apply_inr0, vec4_apply_inr1, h2, h3,
    h4, h5]
  exact ⟨by ring, by ring⟩

theorem shape_plane {T : (Fin 2 ⊕ Fin 2 → K) → (Fin 2 ⊕ Fin 2 → K)}
    (hadd : ∀ x y, T (x + y) = T x + T y) (hsmul : ∀ (c : K) x, T (c • x) = c • T x)
    {μ : K} (h0 : T (vec4 1 0 0 0) = μ • vec4 1 0 0 0)
    (h1 : T (vec4 0 1 0 0) = μ • vec4 0 1 0 0) {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ spPlane K) :
    T v = μ • v := by
  have hv' : v = v (.inl 0) • vec4 1 0 0 0 + v (.inl 1) • vec4 0 1 0 0 :=
    eq_plane v hv.1 hv.2
  rw [hv', hadd, hsmul, hsmul, h0, h1, smul_add, smul_comm μ (v (.inl 0)),
    smul_comm μ (v (.inl 1))]

theorem shape_nu_ne_zero {T : (Fin 2 ⊕ Fin 2 → K) → (Fin 2 ⊕ Fin 2 → K)}
    (hadd : ∀ x y, T (x + y) = T x + T y) (hsmul : ∀ (c : K) x, T (c • x) = c • T x)
    (hinj : Function.Injective T) {μ ν : K} (hμ : μ ≠ 0)
    (h0 : T (vec4 1 0 0 0) = μ • vec4 1 0 0 0) (h1 : T (vec4 0 1 0 0) = μ • vec4 0 1 0 0)
    (h2 : T (vec4 0 0 1 0) (.inr 0) = ν) (h3 : T (vec4 0 0 1 0) (.inr 1) = 0) : ν ≠ 0 := by
  intro hν
  have hP : T (vec4 0 0 1 0) ∈ spPlane K := ⟨h2.trans hν, h3⟩
  have hx : μ⁻¹ • T (vec4 0 0 1 0) ∈ spPlane K := (spPlane K).smul_mem _ hP
  have h := shape_plane hadd hsmul h0 h1 hx
  rw [smul_smul, mul_inv_cancel₀ hμ, one_smul] at h
  have := congrFun (hinj h) (.inr 0)
  rw [Pi.smul_apply, hP.1, smul_zero, vec4_apply_inr0] at this
  exact one_ne_zero this.symm

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

omit [Field K] in
theorem comm_aux (a b c : W) : a * b * (a * c)⁻¹ = b * c⁻¹ := by
  rw [_root_.mul_inv_rev, mul_comm a b, mul_assoc, mul_comm c⁻¹ a⁻¹, mul_inv_cancel_left]

variable [Finite K] [CharP K 2] [Finite W]

theorem tf_eq_id (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K)
    {L : Subgroup (MulAut W)} (hLperf : ⁅L, L⁆ = L) (hLH : ∀ k ∈ L, ∀ h ∈ H, k * h * k⁻¹ ∈ H)
    (hLZ : L ≤ Ch11.SecA.stabW Z)
    (hLU : L ≤ Ch11.SecA.stabW (hf.pre (gmapSp g (spPlane K)).toAddSubgroup))
    (hLc : ∀ k ∈ L, ∀ s ∈ perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmapSp g (spPlane K)).toAddSubgroup)), k * s * k⁻¹ * s⁻¹ ∈ pCoreOf 2
        (perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spPlane K)).toAddSubgroup)))) :
    ∀ k ∈ L, ∀ x, tf hf g k x = x := by
  have hperf : commutator ↥L = ⊤ := by
    rw [commutator_def]
    exact Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hLperf)
  have triv : ∀ {A : Type _} [CommGroup A] (φ : ↥L →* A) (k : ↥L), φ k = 1 := by
    intro A _ φ k
    have := Abelianization.commutator_subset_ker φ
    rw [hperf] at this
    exact this (Subgroup.mem_top k)
  have hkZ : ∀ k ∈ L, ∀ z ∈ Z, k z ∈ Z := fun k hk z hz =>
    (Ch11.SecA.mem_stabW.mp (hLZ hk) z).mp hz
  have hS : ∀ k ∈ L, (∀ x y, tf hf g k (x + y) = tf hf g k x + tf hf g k y) ∧
      (∀ (c : K) x, tf hf g k (c • x) = c • tf hf g k x) ∧
      tf hf g k (vec4 1 0 0 0) (.inl 0) ≠ 0 ∧ tf hf g k (vec4 0 0 1 0) (.inr 0) ≠ 0 ∧
      (∀ v ∈ spPlane K, tf hf g k v = tf hf g k (vec4 1 0 0 0) (.inl 0) • v) ∧
      ∀ v, tf hf g k v (.inr 0) = tf hf g k (vec4 0 0 1 0) (.inr 0) * v (.inr 0) ∧
        tf hf g k v (.inr 1) = tf hf g k (vec4 0 0 1 0) (.inr 0) * v (.inr 1) := by
    intro k hk
    obtain ⟨hadd, hsmul, hinj, μ, ν, hμ0, h0, h1, h2, h3, h4, h5⟩ :=
      tf_shape hK4 hf g (hLZ hk) (hLH k hk) (hLU hk) (hLc k hk)
    have hμ : tf hf g k (vec4 1 0 0 0) (.inl 0) = μ := by
      rw [h0, Pi.smul_apply, vec4_apply_inl0, smul_eq_mul, mul_one]
    rw [hμ, h2]
    exact ⟨hadd, hsmul, hμ0, shape_nu_ne_zero hadd hsmul hinj hμ0 h0 h1 h2 h3,
      fun v hv => shape_plane hadd hsmul h0 h1 hv, shape_inr hadd hsmul h0 h1 h2 h3 h4 h5⟩
  have hμ1 : ∀ k ∈ L, tf hf g k (vec4 1 0 0 0) (.inl 0) = 1 := by
    let φ : ↥L →* Kˣ := MonoidHom.mk' (fun k => Units.mk0 _ (hS k k.2).2.2.1) fun a b => by
      apply Units.ext
      simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul]
      obtain ⟨μb, hμb⟩ : ∃ c, tf hf g b (vec4 1 0 0 0) (.inl 0) = c := ⟨_, rfl⟩
      have e : tf hf g b (vec4 1 0 0 0) = μb • vec4 1 0 0 0 := by
        rw [(hS b b.2).2.2.2.2.1 _ ⟨rfl, rfl⟩, hμb]
      rw [hμb, tf_mul hf g (hkZ a a.2), e, (hS a a.2).2.1, Pi.smul_apply, smul_eq_mul,
        mul_comm]
    intro k hk
    have := congrArg Units.val (triv φ ⟨k, hk⟩)
    simpa [φ] using this
  have hν1 : ∀ k ∈ L, tf hf g k (vec4 0 0 1 0) (.inr 0) = 1 := by
    let φ : ↥L →* Kˣ := MonoidHom.mk' (fun k => Units.mk0 _ (hS k k.2).2.2.2.1) fun a b => by
      apply Units.ext
      simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul]
      rw [tf_mul hf g (hkZ a a.2), ((hS a a.2).2.2.2.2.2 _).1]
    intro k hk
    have := congrArg Units.val (triv φ ⟨k, hk⟩)
    simpa [φ] using this
  have hplane1 : ∀ k ∈ L, ∀ v ∈ spPlane K, tf hf g k v = v := fun k hk v hv => by
    rw [(hS k hk).2.2.2.2.1 v hv, hμ1 k hk, one_smul]
  have hX : ∀ k ∈ L, ∀ v, tf hf g k v - v ∈ spPlane K := fun k hk v => by
    obtain ⟨h0, h1⟩ := (hS k hk).2.2.2.2.2 v
    rw [hν1 k hk, one_mul] at h0 h1
    exact ⟨by rw [Pi.sub_apply, h0, sub_self], by rw [Pi.sub_apply, h1, sub_self]⟩
  have hδmul : ∀ a ∈ L, ∀ b ∈ L, ∀ v,
      tf hf g (a * b) v - v = (tf hf g a v - v) + (tf hf g b v - v) := by
    intro a ha b hb v
    rw [tf_mul hf g (hkZ a ha)]
    have e : tf hf g b v = v + (tf hf g b v - v) := by abel
    rw [e, (hS a ha).1, hplane1 a ha _ (hX b hb v)]
    abel
  intro k hk v
  let φ : ↥L →* Multiplicative (Fin 2 ⊕ Fin 2 → K) :=
    MonoidHom.mk' (fun k => Multiplicative.ofAdd (tf hf g k v - v)) fun a b => by
      show Multiplicative.ofAdd (tf hf g (a * b) v - v) = _
      rw [hδmul a a.2 b b.2 v, ofAdd_add]
  have h1 := triv φ ⟨k, hk⟩
  have h2 : tf hf g k v - v = 0 := by
    have := congrArg Multiplicative.toAdd h1
    simpa [φ] using this
  exact sub_eq_zero.mp h2

theorem perfCent_sp (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (g : StatedSp 2 K) (hcomm : commV H = ⊤) :
    Ch11.SecA.PerfCentFacts H Z (hf.pre (gmapSp g (spPlane K)).toAddSubgroup) := by
  intro L hLperf hLH hLZ hLU hLc k hk w
  have hid := tf_eq_id hK4 hf g hLperf hLH hLZ hLU hLc k hk
  have hkZ : ∀ z ∈ Z, k z ∈ Z := fun z hz => (Ch11.SecA.mem_stabW.mp (hLZ hk) z).mp hz
  have hfk : ∀ v, f (k v) = f v := fun v => by
    have h1 := tf_mk hf g hkZ v
    rw [hid] at h1
    have h2 := congrArg (fun y => mat 2 K g *ᵥ y) h1
    simpa only [mat_mulVec_inv] using h2.symm
  have hkh : ∀ h ∈ H, k * h * k⁻¹ = h := fun h hh =>
    eq_of_forall_f_eq hf (hLH k hk h hh) hh fun v => by
      simp only [MulAut.mul_apply]
      rw [hfk]
      apply act_congr hf hh
      have h1 := hfk (k⁻¹ v)
      rw [MulAut.apply_inv_self] at h1
      exact h1.symm
  let F : Subgroup W :=
    { carrier := {y | k y = y}
      mul_mem' := fun {a b} ha hb => by
        show k (a * b) = a * b
        rw [map_mul, show k a = a from ha, show k b = b from hb]
      one_mem' := map_one k
      inv_mem' := fun {a} ha => by
        show k a⁻¹ = a⁻¹
        rw [map_inv, show k a = a from ha] }
  have hle : commV H ≤ F := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨h, hh, v, rfl⟩
    show k (h v * v⁻¹) = h v * v⁻¹
    have hz : k v * v⁻¹ ∈ Z := (hf.eq_iff _ _).mp (hfk v)
    have e1 : k (h v) = h (k v) := by
      have := congrArg (fun x : MulAut W => x (k v)) (hkh h hh)
      simpa [MulAut.mul_apply] using this
    have e2 : k v = (k v * v⁻¹) * v := by group
    rw [map_mul, map_inv, e1, e2, map_mul, hZ h hh _ hz]
    exact comm_aux _ _ _
  exact hle (hcomm ▸ Subgroup.mem_top w)

end KA

end CFSG.Quasithin.Vol2.KGNat
