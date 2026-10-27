module

public import CFSG.RankThree.GF2n.Smith81.OrthE1B7bHeart
public import CFSG.RankThree.GF2n.Smith81.OrthE1B6Grp

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.B6

open CFSG.RankThree.GF2n.Smith81.OrthTN

section Cube

variable {K : Type} [Field K] [Finite K] [CharP K 2]

instance b6s_finite_aut : Finite (Cube 3 K ≃ₗ[K] Cube 3 K) :=
  Finite.of_injective (fun f : Cube 3 K ≃ₗ[K] Cube 3 K => (f : Cube 3 K → Cube 3 K))
    DFunLike.coe_injective

theorem b6s_comm_cubeU {g h : Cube 3 K ≃ₗ[K] Cube 3 K} (hg : g ∈ cubeU 3 K)
    (hh : h ∈ cubeU 3 K) : g * h = h * g := by
  have h1 := cubeU_mul_self hg
  have h2 := cubeU_mul_self hh
  have h3 := cubeU_mul_self ((cubeU 3 K).mul_mem hg hh)
  have e1 : (g * h)⁻¹ = g * h := inv_eq_of_mul_eq_one_right h3
  have e2 : g⁻¹ = g := inv_eq_of_mul_eq_one_right h1
  have e3 : h⁻¹ = h := inv_eq_of_mul_eq_one_right h2
  rw [mul_inv_rev, e2, e3] at e1
  exact e1.symm

theorem b6s_inter_trivial (hq : 4 ≤ Nat.card K) {i j : Fin 3} (hij : i ≠ j) :
    cubeF 3 K i ⊓ cubeF 3 K j = ⊥ := by
  have hF := threeFactors hq (K := K)
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  exact eq_one_of_mem_of_commute_of_isSimpleGroup (hF.simple i) (hF.nonab i)
    (Subgroup.mem_inf.mp hx).1
    (fun y hy => hF.comm i j hij y hy x (Subgroup.mem_inf.mp hx).2)

theorem b6s_uniKron_mulSingle_mem (a : Fin 3) (β : K) :
    uniKron 3 K (Pi.mulSingle a (Multiplicative.ofAdd β)) ∈ cubeF 3 K a := by
  refine mem_cubeF.mpr ⟨uniMat β, uniMat_det β, fun v => ?_⟩
  show kronMap (fun i => uniMat (Multiplicative.toAdd
    ((Pi.mulSingle a (Multiplicative.ofAdd β) : Fin 3 → Multiplicative K) i))) v =
      actMap a (uniMat β) v
  unfold actMap
  congr 2
  funext i
  by_cases h : i = a
  · subst h
    simp
  · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h]
    simp [uniMat_zero]

theorem b6s_card_T (a : Fin 3) :
    Nat.card K ≤ Nat.card ↥(cubeU 3 K ⊓ cubeF 3 K a) := by
  let f : K → ↥(cubeU 3 K ⊓ cubeF 3 K a) := fun β =>
    ⟨uniKron 3 K (Pi.mulSingle a (Multiplicative.ofAdd β)),
      Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, b6s_uniKron_mulSingle_mem a β⟩⟩
  refine Nat.card_le_card_of_injective f fun β γ h => ?_
  have h1 := congrArg Subtype.val h
  have h2 := uniKron_injective 3 K h1
  have h3 := congrFun h2 a
  simpa using h3

theorem b6s_mem_cubeU_of_fix (hq : 4 ≤ Nat.card K) (T : Cube 3 K ≃ₗ[K] Cube 3 K)
    (hπ : ∀ (i : Fin 3) (x : Cube 3 K ≃ₗ[K] Cube 3 K),
      x ∈ cubeF 3 K i ↔ T * x * T⁻¹ ∈ cubeF 3 K i)
    (hU' : ∀ x ∈ cubeU 3 K, T⁻¹ * x * T ∈ cubeU 3 K)
    (hT2 : T * T ∈ cubeU 3 K) : T ∈ cubeU 3 K := by
  have hL3 : ∀ i : Fin 3, ∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 →
      ∃ A' : Matrix (Fin 2) (Fin 2) K, A'.det = 1 ∧
        ∀ v, T (actMap i A v) = actMap ((1 : Equiv.Perm (Fin 3)) i) A' (T v) := by
    intro i A hA
    have hx := actSL_mem i (mkSL A hA)
    have h1 := (hπ i _).mp hx
    obtain ⟨A', hA', hv⟩ := mem_cubeF.mp h1
    refine ⟨A', hA', fun v => ?_⟩
    have h2 := hv (T v)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      show T⁻¹ (T v) = v from T.symm_apply_apply v, actSL_apply] at h2
    exact h2
  obtain ⟨h, hunit, hTh⟩ := exists_kron_perm T 1 hL3
  have hfix : ∀ g ∈ cubeU 3 K, g (T (cubeZero 3 K)) = T (cubeZero 3 K) := by
    intro g hg
    obtain ⟨β, hβ⟩ := mem_cubeU.mp (hU' g hg)
    have h1 : (T⁻¹ * g * T) (cubeZero 3 K) = cubeZero 3 K := by
      rw [hβ, kronMap_uni_cubeZero]
    have h2 := congrArg T h1
    simpa using h2
  obtain ⟨c, hc⟩ := fixed_of_cubeU (T (cubeZero 3 K)) hfix
  have hup : ∀ i, h i 1 0 = 0 := by
    refine upper_of_kron_cubeZero h hunit c ?_
    have hz : T (cubeZero 3 K) = kronMap h (cubeZero 3 K) := by
      rw [hTh, permMap_cubeZero]
    rw [← hz]
    exact hc
  refine b7b_mem_cubeU_of_upper hq T h hunit hup (fun v => ?_) hT2
  rw [hTh v, permMap_one]
  rfl

theorem b6s_perm_unique (hq : 4 ≤ Nat.card K) {s : Cube 3 K ≃ₗ[K] Cube 3 K}
    {π π' : Equiv.Perm (Fin 3)}
    (h1 : ∀ (i : Fin 3) (x : Cube 3 K ≃ₗ[K] Cube 3 K),
      x ∈ cubeF 3 K i ↔ s * x * s⁻¹ ∈ cubeF 3 K (π i))
    (h2 : ∀ (i : Fin 3) (x : Cube 3 K ≃ₗ[K] Cube 3 K),
      x ∈ cubeF 3 K i ↔ s * x * s⁻¹ ∈ cubeF 3 K (π' i)) : π = π' := by
  have hF := threeFactors hq (K := K)
  refine Equiv.ext fun i => ?_
  by_contra hne
  apply hF.ne hne
  refine Subgroup.ext fun y => ?_
  have e : s * (s⁻¹ * y * s) * s⁻¹ = y := by group
  have a1 : y ∈ cubeF 3 K (π i) ↔ s⁻¹ * y * s ∈ cubeF 3 K i := by
    rw [h1 i (s⁻¹ * y * s), e]
  have a2 : y ∈ cubeF 3 K (π' i) ↔ s⁻¹ * y * s ∈ cubeF 3 K i := by
    rw [h2 i (s⁻¹ * y * s), e]
  rw [a1, a2]

theorem b6s_exists_hom (hq : 4 ≤ Nat.card K) (S : Subgroup (Cube 3 K ≃ₗ[K] Cube 3 K))
    (hS : ∀ s ∈ S, (∀ x ∈ cubeE 3 K, s * x * s⁻¹ ∈ cubeE 3 K) ∧
      (∀ x ∈ cubeE 3 K, s⁻¹ * x * s ∈ cubeE 3 K)) :
    ∃ φ : S →* Equiv.Perm (Fin 3), ∀ (s : S) (i : Fin 3) (x : Cube 3 K ≃ₗ[K] Cube 3 K),
      x ∈ cubeF 3 K i ↔
        (s : Cube 3 K ≃ₗ[K] Cube 3 K) * x * (s : Cube 3 K ≃ₗ[K] Cube 3 K)⁻¹ ∈
          cubeF 3 K (φ s i) := by
  have hF := threeFactors hq (K := K)
  have hex : ∀ s : S, ∃ π : Equiv.Perm (Fin 3), ∀ (i : Fin 3) (x : Cube 3 K ≃ₗ[K] Cube 3 K),
      x ∈ cubeF 3 K i ↔ (s : Cube 3 K ≃ₗ[K] Cube 3 K) * x * (s : Cube 3 K ≃ₗ[K] Cube 3 K)⁻¹ ∈
        cubeF 3 K (π i) :=
    fun s => hF.exists_perm s (hS s s.2).1 (hS s s.2).2
  choose f hf using hex
  refine ⟨MonoidHom.mk' f fun s t => ?_, hf⟩
  refine b6s_perm_unique hq (hf (s * t)) ?_
  intro i x
  rw [hf t i x, hf s (f t i)]
  have e : ((s * t : S) : Cube 3 K ≃ₗ[K] Cube 3 K) * x *
      ((s * t : S) : Cube 3 K ≃ₗ[K] Cube 3 K)⁻¹ =
      (s : Cube 3 K ≃ₗ[K] Cube 3 K) * ((t : Cube 3 K ≃ₗ[K] Cube 3 K) * x *
        (t : Cube 3 K ≃ₗ[K] Cube 3 K)⁻¹) * (s : Cube 3 K ≃ₗ[K] Cube 3 K)⁻¹ := by
    simp [mul_assoc]
  rw [e]
  rfl

end Cube

section Normalizer

variable {G : Type*} [Group G]

theorem b6s_inv_conj_mem {U : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (U : Set G))
    {x : G} (hx : x ∈ U) : t⁻¹ * x * t ∈ U := by
  have h := (Subgroup.mem_normalizer_iff.mp ht (t⁻¹ * x * t)).mpr
  have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
  exact h (by rw [e]; exact hx)

end Normalizer

section Cube

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem b6s_main_hom (hq : 4 ≤ Nat.card K) (S : Subgroup (Cube 3 K ≃ₗ[K] Cube 3 K))
    (hS2 : IsPGroup 2 S)
    (hSn : ∀ s ∈ S, s ∈ Subgroup.normalizer (cubeU 3 K : Set (Cube 3 K ≃ₗ[K] Cube 3 K)) ∧
      (∀ x ∈ cubeE 3 K, s * x * s⁻¹ ∈ cubeE 3 K) ∧
      (∀ x ∈ cubeE 3 K, s⁻¹ * x * s ∈ cubeE 3 K)) :
    ∃ φ : S →* Equiv.Perm (Fin 3),
      (∀ (s : S) (i : Fin 3) (x : Cube 3 K ≃ₗ[K] Cube 3 K), x ∈ cubeF 3 K i ↔
        (s : Cube 3 K ≃ₗ[K] Cube 3 K) * x * (s : Cube 3 K ≃ₗ[K] Cube 3 K)⁻¹ ∈
          cubeF 3 K (φ s i)) ∧
      ∀ s : S, φ s = 1 ↔ (s : Cube 3 K ≃ₗ[K] Cube 3 K) ∈ cubeU 3 K := by
  have hF := threeFactors hq (K := K)
  obtain ⟨φ, hφ⟩ := b6s_exists_hom hq S fun s hs => ⟨(hSn s hs).2.1, (hSn s hs).2.2⟩
  refine ⟨φ, hφ, fun s => ⟨fun h1 => ?_, fun hsU => ?_⟩⟩
  · by_contra hsU
    obtain ⟨m, hm⟩ := hS2 s
    have hm' : (s : Cube 3 K ≃ₗ[K] Cube 3 K) ^ (2 ^ m) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    obtain ⟨k, hk1, hk2⟩ := b6s_exists_sq_mem (cubeU 3 K) m (s : Cube 3 K ≃ₗ[K] Cube 3 K) hsU
      (by rw [hm']; exact one_mem _)
    have hφt : φ (s ^ k) = 1 := by rw [map_pow, h1, one_pow]
    have hcoe : ((s ^ k : S) : Cube 3 K ≃ₗ[K] Cube 3 K) =
        (s : Cube 3 K ≃ₗ[K] Cube 3 K) ^ k := rfl
    apply hk1
    rw [← hcoe]
    refine b6s_mem_cubeU_of_fix hq _ ?_ ?_ ?_
    · intro i x
      have := hφ (s ^ k) i x
      rwa [hφt] at this
    · intro x hx
      exact b6s_inv_conj_mem (hSn _ (s ^ k).2).1 hx
    · rw [hcoe]
      exact hk2
  · refine b6s_perm_unique hq (hφ s) ?_
    intro i x
    exact hF.conj_iff i (cubeU_le_cubeE hsU) x

theorem b6s_relIndex_le_two {S : Subgroup (Cube 3 K ≃ₗ[K] Cube 3 K)} (hS2 : IsPGroup 2 S)
    (φ : S →* Equiv.Perm (Fin 3))
    (hker : ∀ s : S, φ s = 1 ↔ (s : Cube 3 K ≃ₗ[K] Cube 3 K) ∈ cubeU 3 K) :
    (cubeU 3 K).relIndex S ≤ 2 := by
  have hk : φ.ker = (cubeU 3 K).subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]
  have h1 : (cubeU 3 K).relIndex S = Nat.card φ.range := by
    rw [Subgroup.relIndex, ← hk, Subgroup.index_ker]
  have h2 : Nat.card φ.range ∣ 6 := by
    have := Subgroup.card_subgroup_dvd_card φ.range
    rwa [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 3)), Fintype.card_perm,
      Fintype.card_fin] at this
  obtain ⟨n, hn⟩ := IsPGroup.index hS2 ((cubeU 3 K).subgroupOf S)
  have h3 : 2 ^ n ∣ 6 := by
    rw [← hn, ← Subgroup.relIndex, h1]
    exact h2
  rw [Subgroup.relIndex, hn]
  rcases n with _ | _ | n
  · norm_num
  · norm_num
  · exfalso
    have h4 : 4 ∣ 2 ^ (n + 2) := ⟨2 ^ n, by ring⟩
    have := h4.trans h3
    omega

theorem b6s_centralizer_lt (hq : 4 ≤ Nat.card K) {S : Subgroup (Cube 3 K ≃ₗ[K] Cube 3 K)}
    (φ : S →* Equiv.Perm (Fin 3))
    (hφ : ∀ (s : S) (i : Fin 3) (x : Cube 3 K ≃ₗ[K] Cube 3 K), x ∈ cubeF 3 K i ↔
      (s : Cube 3 K ≃ₗ[K] Cube 3 K) * x * (s : Cube 3 K ≃ₗ[K] Cube 3 K)⁻¹ ∈
        cubeF 3 K (φ s i))
    (hker : ∀ s : S, φ s = 1 ↔ (s : Cube 3 K ≃ₗ[K] Cube 3 K) ∈ cubeU 3 K) :
    ∀ s ∈ S, s ∉ cubeU 3 K →
      2 * Nat.card ↥(cubeU 3 K ⊓ Subgroup.centralizer ({s} : Set (Cube 3 K ≃ₗ[K] Cube 3 K))) <
        Nat.card (cubeU 3 K) := by
  intro s hsS hsU
  have hne : φ ⟨s, hsS⟩ ≠ 1 := fun h => hsU ((hker ⟨s, hsS⟩).mp h)
  obtain ⟨a, ha⟩ : ∃ a, φ ⟨s, hsS⟩ a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact hne (Equiv.ext hcon)
  have hTC : (cubeU 3 K ⊓ cubeF 3 K a) ⊓
      (cubeU 3 K ⊓ Subgroup.centralizer ({s} : Set (Cube 3 K ≃ₗ[K] Cube 3 K))) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun u hu => ?_
    simp only [Subgroup.mem_inf] at hu
    obtain ⟨⟨huU, huA⟩, -, huC⟩ := hu
    have hc : s * u = u * s := Subgroup.mem_centralizer_iff.mp huC s (Set.mem_singleton s)
    have h1 : s * u * s⁻¹ ∈ cubeF 3 K (φ ⟨s, hsS⟩ a) := (hφ ⟨s, hsS⟩ a u).mp huA
    have h2 : s * u * s⁻¹ = u := by rw [hc]; group
    rw [h2] at h1
    have h3 := b6s_inter_trivial hq (Ne.symm ha)
    rw [Subgroup.eq_bot_iff_forall] at h3
    exact h3 u (Subgroup.mem_inf.mpr ⟨huA, h1⟩)
  have hTN : (cubeU 3 K ⊓ cubeF 3 K a) ≤ Subgroup.normalizer
      ((cubeU 3 K ⊓ Subgroup.centralizer ({s} : Set (Cube 3 K ≃ₗ[K] Cube 3 K)) :
        Subgroup (Cube 3 K ≃ₗ[K] Cube 3 K)) : Set (Cube 3 K ≃ₗ[K] Cube 3 K)) := by
    refine Subgroup.le_normalizer_iff.mpr fun t ht c hc => ?_
    have h1 := (Subgroup.mem_inf.mp ht).1
    have h2 := (Subgroup.mem_inf.mp hc).1
    rw [b6s_comm_cubeU h1 h2, mul_assoc, mul_inv_cancel, mul_one]
    exact hc
  have hprod := b7b_card_sup_mul_card_inf hTN
  rw [hTC, Subgroup.card_bot, mul_one] at hprod
  have hle : Nat.card ↥((cubeU 3 K ⊓ cubeF 3 K a) ⊔
      (cubeU 3 K ⊓ Subgroup.centralizer ({s} : Set (Cube 3 K ≃ₗ[K] Cube 3 K)))) ≤
      Nat.card (cubeU 3 K) :=
    Subgroup.card_le_of_le (sup_le inf_le_left inf_le_left)
  have hT := b6s_card_T (K := K) a
  rw [card_cubeU] at hle ⊢
  set q := Nat.card K with hqdef
  set c := Nat.card ↥(cubeU 3 K ⊓ Subgroup.centralizer ({s} : Set (Cube 3 K ≃ₗ[K] Cube 3 K)))
    with hcdef
  have hq0 : 0 < q := by omega
  have h1 : q * c ≤ q ^ 3 := by
    calc q * c ≤ Nat.card ↥(cubeU 3 K ⊓ cubeF 3 K a) * c := Nat.mul_le_mul_right _ hT
      _ ≤ q ^ 3 := by rw [← hprod]; exact hle
  have h2 : c ≤ q ^ 2 := by
    refine Nat.le_of_mul_le_mul_left ?_ hq0
    calc q * c ≤ q ^ 3 := h1
      _ = q * q ^ 2 := by ring
  have h3 : 0 < q ^ 2 := by positivity
  nlinarith

end Cube

theorem b6_index_two {K : Type} [Field K] [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (P : Subgroup (Cube 3 K ≃ₗ[K] Cube 3 K)) (hP : IsPGroup 2 P) (hUP : cubeU 3 K ≤ P)
    (hnorm : ∀ s ∈ P, s ∈ Subgroup.normalizer (cubeU 3 K : Set (Cube 3 K ≃ₗ[K] Cube 3 K)) →
      (∀ x ∈ cubeE 3 K, s * x * s⁻¹ ∈ cubeE 3 K) ∧ (∀ x ∈ cubeE 3 K, s⁻¹ * x * s ∈ cubeE 3 K)) :
    (cubeU 3 K).relIndex P ≤ 2 := by
  have hUS : cubeU 3 K ≤
      P ⊓ Subgroup.normalizer (cubeU 3 K : Set (Cube 3 K ≃ₗ[K] Cube 3 K)) :=
    le_inf hUP Subgroup.le_normalizer
  have hS2 : IsPGroup 2
      ↥(P ⊓ Subgroup.normalizer (cubeU 3 K : Set (Cube 3 K ≃ₗ[K] Cube 3 K))) :=
    hP.to_le inf_le_left
  obtain ⟨φ, hφ, hker⟩ := b6s_main_hom hq
    (P ⊓ Subgroup.normalizer (cubeU 3 K : Set (Cube 3 K ≃ₗ[K] Cube 3 K))) hS2
    fun s hs => ⟨hs.2, hnorm s hs.1 hs.2⟩
  have hidx := b6s_relIndex_le_two hS2 φ hker
  have hcent := b6s_centralizer_lt hq φ hφ hker
  have hkey : ∀ V : Subgroup (Cube 3 K ≃ₗ[K] Cube 3 K),
      V ≤ P ⊓ Subgroup.normalizer (cubeU 3 K : Set (Cube 3 K ≃ₗ[K] Cube 3 K)) →
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) → Nat.card V = Nat.card (cubeU 3 K) →
      V = cubeU 3 K := fun V hVS hVab hcard =>
    b6s_unique_abelian hUS inf_le_right hidx hcent hVS hVab hcard
  have hSP := b6s_S_eq_P hP hUP (fun x hx y hy => b6s_comm_cubeU hx hy) hkey
  rw [hSP] at hidx
  exact hidx

end CFSG.RankThree.GF2n.Smith81.Smith23E1.B6

end
