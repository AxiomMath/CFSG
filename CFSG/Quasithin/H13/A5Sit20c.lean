module

public import CFSG.Quasithin.H13.A5Sit
public import CFSG.Quasithin.H13.A5S1520c
public import CFSG.Quasithin.H13.A5S1520b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5 (Hstar piQ piQ_surjective piQ_eq_one_iff eq_mul_conj_of_inv
  mul_inv_of_inv mul_eq_of_inv e9_fix_mul)

namespace A5Sit

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  (S : A5Sit G T V V₁ V₃ L₁ H)
include S

theorem UH_le_normalizer_V1 :
    conjClosure V₃ H ≤ Subgroup.normalizer (V₁ : Set G) :=
  (S.hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans
    S.hF.H_normalizes_V₁

theorem normal_V1_UH :
    (V₁.subgroupOf (conjClosure V₃ H)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (S.V1_le_V3.trans (le_conjClosure V₃ H))).mpr (S.UH_le_normalizer_V1)

theorem exists_actQ [(V₁.subgroupOf (conjClosure V₃ H)).Normal] :
    ∃ ρ : Hstar H →* Monoid.End (↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)),
      ∀ (h : ↥H) (u u' : ↥(conjClosure V₃ H)), (u' : G) = h * u * (h : G)⁻¹ →
        ρ (piQ H h) (u : ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) = u' := by
  have hF := S.hF
  have hUn : H ≤ Subgroup.normalizer (conjClosure V₃ H : Set G) :=
    le_normalizer_conjClosure V₃ H
  have hV1n : H ≤ Subgroup.normalizer (V₁ : Set G) := hF.H_normalizes_V₁
  let cU : ↥H → ↥(conjClosure V₃ H) →* ↥(conjClosure V₃ H) := fun h =>
    { toFun := fun u => ⟨(h : G) * u * (h : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hUn h.2) u).mp u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u u' => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcN : ∀ h : ↥H, V₁.subgroupOf (conjClosure V₃ H) ≤
      (V₁.subgroupOf (conjClosure V₃ H)).comap (cU h) := by
    intro h u hu
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hu
    exact (Subgroup.mem_normalizer_iff.mp (hV1n h.2) u).mp hu
  let act : ↥H → Monoid.End (↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) :=
    fun h => QuotientGroup.map _ _ (cU h) (hcN h)
  let ρ0 : ↥H →* Monoid.End (↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) :=
    { toFun := act
      map_one' := by
        refine MonoidHom.ext fun w => ?_
        obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective w
        show ((cU 1 u : ↥(conjClosure V₃ H)) :
          ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) = u
        congr 1
        exact Subtype.ext (by simp [cU])
      map_mul' := fun h k => by
        refine MonoidHom.ext fun w => ?_
        obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective w
        show ((cU (h * k) u : ↥(conjClosure V₃ H)) :
          ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) = (cU h (cU k u) : _)
        congr 1
        exact Subtype.ext (by simp only [cU, MonoidHom.coe_mk, OneHom.coe_mk,
          Subgroup.coe_mul, mul_inv_rev]; group) }
  have hker : (pCoreOf 2 H).subgroupOf H ≤ ρ0.ker := by
    intro q hq
    rw [Subgroup.mem_subgroupOf] at hq
    rw [MonoidHom.mem_ker]
    refine MonoidHom.ext fun w => ?_
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective w
    show ((cU q u : ↥(conjClosure V₃ H)) :
      ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) = u
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hqC := hF.pCoreOf_eq_centralizerMod ▸ hq
    have := hqC.2.2 _ (Subgroup.inv_mem _ u.2)
    simp only [cU, MonoidHom.coe_mk, OneHom.coe_mk, inv_inv] at this ⊢
    simpa [mul_assoc] using this
  refine ⟨QuotientGroup.lift _ ρ0 hker, fun h u u' hu' => ?_⟩
  show ((cU h u : ↥(conjClosure V₃ H)) :
    ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) = u'
  congr 1
  exact Subtype.ext hu'.symm

theorem UH_quot_comm [(V₁.subgroupOf (conjClosure V₃ H)).Normal]
    (a b : ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) : a * b = b * a := by
  have hF := S.hF
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have := hF.commutator_conjClosure_le _ (Subgroup.inv_mem _ u'.2) _
    (hF.conjClosure_Vp_le_pCoreOf (Subgroup.inv_mem _ u.2))
  simpa [mul_assoc] using this

theorem UH_quot_sq [(V₁.subgroupOf (conjClosure V₃ H)).Normal]
    (a : ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) : a * a = 1 := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have := S.hF.sq_mem_conjClosure _ u.2
  simpa [pow_two] using this

theorem comm_inter_eq [(V₁.subgroupOf (conjClosure V₃ H)).Normal]
    (ρ : Hstar H →* Monoid.End (↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)))
    (hρ : ∀ (h : ↥H) (u u' : ↥(conjClosure V₃ H)), (u' : G) = h * u * (h : G)⁻¹ →
        ρ (piQ H h) (u : ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) = u')
    {v : G} (hv : v ∈ V) (hvQ : v ∉ pCoreOf 2 H) {s : Hstar H} (hs : s ^ 3 = 1) (hs1 : s ≠ 1)
    (hbs : piQ H ⟨v, S.V_le_H hv⟩ * s * piQ H ⟨v, S.V_le_H hv⟩ = s⁻¹)
    (a a' : ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H))
    (h : ρ (piQ H ⟨v, S.V_le_H hv⟩) a / a =
      ρ s (ρ (piQ H ⟨v, S.V_le_H hv⟩) a' / a')) :
    ρ (piQ H ⟨v, S.V_le_H hv⟩) a = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := S.hF
  have hVH := S.V_le_H
  have hVQ : ¬ V ≤ pCoreOf 2 H := fun h => hvQ (h hv)
  obtain ⟨-, hUV, -⟩ := hF.F95_2_aux S.relIndex_V3 hVQ
  have hUn : H ≤ Subgroup.normalizer (conjClosure V₃ H : Set G) :=
    le_normalizer_conjClosure V₃ H
  have hV1n : H ≤ Subgroup.normalizer (V₁ : Set G) := hF.H_normalizes_V₁
  have hmemU : ∀ (h : ↥H) (u : ↥(conjClosure V₃ H)), (h : G) * u * (h : G)⁻¹ ∈
      conjClosure V₃ H := fun h u => (Subgroup.mem_normalizer_iff.mp (hUn h.2) u).mp u.2
  have hcV3 : ∀ u : ↥(conjClosure V₃ H), v * u * v⁻¹ * (u : G)⁻¹ ∈ V₃ := by
    intro u
    have h1 := hUV (Subgroup.commutator_mem_commutator u.2 hv)
    have h2 := V₃.inv_mem h1
    rw [commutatorElement_inv, commutatorElement_def] at h2
    exact h2
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨ŝ, rfl⟩ := piQ_surjective H s
  have e1 := hρ ⟨v, hVH hv⟩ w ⟨_, hmemU ⟨v, hVH hv⟩ w⟩ rfl
  have e2 := hρ ⟨v, hVH hv⟩ w' ⟨_, hmemU ⟨v, hVH hv⟩ w'⟩ rfl
  have e3 := hρ ŝ (⟨_, hmemU ⟨v, hVH hv⟩ w'⟩ / w')
    ⟨_, hmemU ŝ (⟨_, hmemU ⟨v, hVH hv⟩ w'⟩ / w')⟩ rfl
  rw [e1, e2, ← QuotientGroup.mk_div, ← QuotientGroup.mk_div, e3, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at h
  rw [e1, ← div_eq_one, ← QuotientGroup.mk_div, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  set t : G := v * w * v⁻¹ * (w : G)⁻¹ with htdef
  set t0 : G := v * w' * v⁻¹ * (w' : G)⁻¹ with ht0def
  have h' : t⁻¹ * ((ŝ : G) * t0 * (ŝ : G)⁻¹) ∈ V₁ := by
    simpa [htdef, ht0def, div_eq_mul_inv, mul_assoc] using h
  rw [Subgroup.coe_div, div_eq_mul_inv]
  show t ∈ V₁
  by_contra ht
  have ht3 : t ∈ V₃ := hcV3 w
  have ht03 : t0 ∈ V₃ := hcV3 w'
  have hs3 : (ŝ : G) * t0 * (ŝ : G)⁻¹ ∈ V₃ := by
    have := V₃.mul_mem ht3 (S.V1_le_V3 h')
    simpa [mul_assoc] using this
  have hsV1 : (ŝ : G) * t0 * (ŝ : G)⁻¹ ∉ V₁ := fun h1 => ht (by
    have := V₁.mul_mem h1 (V₁.inv_mem h')
    simpa [mul_assoc] using this)
  have hsconj : (ŝ : G) * t0 * (ŝ : G)⁻¹ ∈ conjSub (ŝ : G) V := by
    rw [mem_conjSub]
    have e : (ŝ : G)⁻¹ * ((ŝ : G) * t0 * (ŝ : G)⁻¹) * ŝ = t0 := by group
    rw [e]
    exact S.V3_le_V ht03
  have hV1c : V₁ ≤ conjSub (ŝ : G) V := by
    intro z hz
    rw [mem_conjSub]
    have := (Subgroup.mem_normalizer_iff.mp (hV1n (H.inv_mem ŝ.2)) z).mp hz
    rw [inv_inv] at this
    exact S.V1_le_V this
  have hlt : V₁ < V ⊓ conjSub ((ŝ : G)⁻¹)⁻¹ V := by
    rw [inv_inv]
    refine lt_of_le_of_ne (le_inf S.V1_le_V hV1c) fun heq => hsV1 ?_
    rw [heq]
    exact ⟨S.V3_le_V hs3, hsconj⟩
  have hpg := S.isPGroup_sup _ (H.inv_mem ŝ.2) hlt
  rw [inv_inv] at hpg
  have hy : v * ((ŝ : G) * v * (ŝ : G)⁻¹) ∈ V ⊔ conjSub (ŝ : G) V := by
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right ?_)
    rw [mem_conjSub]
    have e : (ŝ : G)⁻¹ * ((ŝ : G) * v * (ŝ : G)⁻¹) * ŝ = v := by group
    rw [e]
    exact hv
  obtain ⟨k, hk⟩ := hpg ⟨_, hy⟩
  have hk' : (v * ((ŝ : G) * v * (ŝ : G)⁻¹)) ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hb2 : piQ H ⟨v, hVH hv⟩ * piQ H ⟨v, hVH hv⟩ = 1 := by
    rw [← map_mul, piQ_eq_one_iff]
    show v * v ∈ pCoreOf 2 H
    rw [S.sq_eq_one_of_mem_V hv]
    exact Subgroup.one_mem _
  have himg : piQ H ⟨v * ((ŝ : G) * v * (ŝ : G)⁻¹),
      H.mul_mem (hVH hv) (H.mul_mem (H.mul_mem ŝ.2 (hVH hv)) (H.inv_mem ŝ.2))⟩ = piQ H ŝ := by
    rw [← eq_mul_conj_of_inv hb2 hs hbs, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  have hs2 : piQ H ŝ ^ 2 ^ k = 1 := by
    rw [← himg, ← map_pow, piQ_eq_one_iff]
    have : ((⟨_, H.mul_mem (hVH hv) (H.mul_mem (H.mul_mem ŝ.2 (hVH hv)) (H.inv_mem ŝ.2))⟩ :
        ↥H) ^ 2 ^ k : ↥H) = 1 := Subtype.ext (by simpa using hk')
    rw [this]
    exact Subgroup.one_mem _
  have h1 : orderOf (piQ H ŝ) ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hs) (orderOf_dvd_of_pow_eq_one hs2)
  rw [Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2), Nat.dvd_one,
    orderOf_eq_one_iff] at h1
  exact hs1 h1

theorem not_e9_inverted {v : G} (hv : v ∈ V) (hvQ : v ∉ pCoreOf 2 H)
    {x y : Hstar H} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : x * y = y * x)
    (hbx : piQ H ⟨v, S.V_le_H hv⟩ * x * piQ H ⟨v, S.V_le_H hv⟩ = x⁻¹)
    (hby : piQ H ⟨v, S.V_le_H hv⟩ * y * piQ H ⟨v, S.V_le_H hv⟩ = y⁻¹)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy1 : x * y ≠ 1) (hxy2 : x * (y * y) ≠ 1) : False := by
  have := S.normal_V1_UH
  obtain ⟨ρ, hρ⟩ := S.exists_actQ
  have hF := S.hF
  have hVH := S.V_le_H
  have hb2 : piQ H ⟨v, hVH hv⟩ * piQ H ⟨v, hVH hv⟩ = 1 := by
    rw [← map_mul, piQ_eq_one_iff]
    show v * v ∈ pCoreOf 2 H
    rw [S.sq_eq_one_of_mem_V hv]
    exact Subgroup.one_mem _
  have hρmul : ∀ g k (a : ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)),
      ρ (g * k) a = ρ g (ρ k a) := fun g k a => by rw [map_mul]; rfl
  have hρone : ∀ a : ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H),
      ρ 1 a = a := fun a => by rw [map_one]; rfl
  have hcube : ∀ s : Hstar H, s ^ 3 = 1 → ∀ a, ρ s (ρ s (ρ s a)) = a := by
    intro s hs a
    rw [← hρmul, ← hρmul, ← pow_three', hs, hρone]
  have hinv : ∀ s : Hstar H, s ^ 3 = 1 →
      piQ H ⟨v, hVH hv⟩ * s * piQ H ⟨v, hVH hv⟩ = s⁻¹ →
      ∀ a, ρ (piQ H ⟨v, hVH hv⟩) (ρ s a) = ρ s (ρ s (ρ (piQ H ⟨v, hVH hv⟩) a)) := by
    intro s hs hbs a
    rw [← hρmul, ← hρmul, ← hρmul, mul_eq_of_inv hb2 hs hbs]
  have hcxy : Commute x y := hxy
  have hyy3 : (y * y) ^ 3 = 1 := by rw [(Commute.refl y).mul_pow, hy, one_mul]
  have hxy3 : (x * y) ^ 3 = 1 := by rw [hcxy.mul_pow, hx, hy, one_mul]
  have hxyy3 : (x * (y * y)) ^ 3 = 1 := by
    rw [(hcxy.mul_right hcxy).mul_pow, hx, hyy3, one_mul]
  have hbyy := mul_inv_of_inv hb2 hby hby rfl
  have hbxy := mul_inv_of_inv hb2 hbx hby hxy
  have hbxyy := mul_inv_of_inv hb2 hbx hbyy (hcxy.mul_right hcxy).eq
  have hxyc : ∀ a, ρ x (ρ y a) = ρ y (ρ x a) := fun a => by rw [← hρmul, ← hρmul, hxy]
  let _ : CommGroup (↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) :=
    { (inferInstance : Group (↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)))
      with mul_comm := S.UH_quot_comm }
  have hfix := e9_fix_mul (S.UH_quot_sq) (ρ (piQ H ⟨v, hVH hv⟩)) (ρ x) (ρ y)
    (hcube x hx) (hcube y hy) hxyc (hinv x hx hbx)
    (hinv y hy hby)
    (fun a a' h => S.comm_inter_eq ρ hρ hv hvQ hx hx1 hbx a a' h)
    (fun a a' h => S.comm_inter_eq ρ hρ hv hvQ hy hy1 hby a a' h)
    (fun a a' h => S.comm_inter_eq ρ hρ hv hvQ hxy3 hxy1 hbxy a a'
      (by rw [hρmul]; exact h))
    (fun a a' h => S.comm_inter_eq ρ hρ hv hvQ hxyy3 hxy2 hbxyy a a'
      (by rw [hρmul, hρmul]; exact h))
  apply hvQ
  rw [hF.pCoreOf_eq_centralizerMod]
  refine ⟨hVH hv, hF.H_normalizes_V₁ (hVH hv), fun u hu => ?_⟩
  have hu' : u⁻¹ ∈ conjClosure V₃ H := Subgroup.inv_mem _ hu
  have hmem : v * u⁻¹ * v⁻¹ ∈ conjClosure V₃ H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V₃ H (hVH hv)) _).mp hu'
  have e := hρ ⟨v, hVH hv⟩ ⟨u⁻¹, hu'⟩ ⟨_, hmem⟩ rfl
  have h1 : ((⟨_, hmem⟩ : ↥(conjClosure V₃ H)) :
      ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) =
        ((⟨u⁻¹, hu'⟩ : ↥(conjClosure V₃ H)) :
          ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) :=
    e.symm.trans (hfix _)
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
  simpa [mul_assoc] using h1

end A5Sit

end CFSG.Quasithin.H13
