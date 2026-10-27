module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3NineAAAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3TData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3P9
public import CFSG.LinearAlgebra.OrderThreeSemilinearAction
public import CFSG.GroupTheory.PrimeOrderSubgroups
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts3A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LinearAlgebra
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open scoped commutatorElement

private theorem s16h_e3_Z3NineAAA_cent_le_normalizer {W : Type} [CommGroup W] [Finite W]
    {A L L₂ : Subgroup (MulAut W)} {x : MulAut W} (hB : s16h_Z3Blocks A L L₂ x)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6) :
    A ⊓ centSub (commSub (⊤ : Subgroup W) L₂) ≤
      A ⊓ Subgroup.normalizer (L : Set (MulAut W)) := by
  rintro k ⟨hkA, hkU₂⟩
  refine ⟨hkA, ?_⟩
  change k ∈ Subgroup.normalizer (L : Set (MulAut W))
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hkL₂ : L.map (MulAut.conj k).toMonoidHom = L₂ := by
    rcases hB.perm k hkA with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 hne
    · exact h1
  set U : Subgroup W := commSub (⊤ : Subgroup W) L with hU
  set U₂ : Subgroup W := commSub (⊤ : Subgroup W) L₂ with hU₂
  have hkU₂_map : ∀ u ∈ U, k u ∈ U₂ := fun u hu =>
    commSub_top_map151b (X := L) (Y := L₂) (g := k)
      (fun l hl => by
        have h := Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hl
        rwa [hkL₂] at h) u hu
  have hk1U₂ : k⁻¹ ∈ centSub U₂ := (centSub U₂).inv_mem hkU₂
  have hUle : U ≤ U₂ := by
    intro u hu
    have h1 : k u ∈ U₂ := hkU₂_map u hu
    have h3 : k⁻¹ (k u) = k u := mem_centSub.mp hk1U₂ (k u) h1
    rw [MulAut.inv_apply_self] at h3
    rwa [← h3] at h1
  have hUbot : U = ⊥ := by
    rw [← le_bot_iff]
    calc U ≤ U ⊓ U₂ := le_inf le_rfl hUle
      _ = ⊥ := by simpa only [hU, hU₂] using hB.inf
  have hrkU : rk U = 6 := by simpa only [hU] using hrk
  rw [hUbot, rk_bot] at hrkU
  omega

private theorem s16h_e3_Z3NineAAA_cent_inf_cent_bot {W : Type} [CommGroup W]
    {A L L₂ : Subgroup (MulAut W)} {x : MulAut W} (hB : s16h_Z3Blocks A L L₂ x) :
    (A ⊓ centSub (commSub (⊤ : Subgroup W) L₂)) ⊓ centSub (commSub (⊤ : Subgroup W) L) = ⊥ := by
  rw [eq_bot_iff_forall]
  intro y hy
  obtain ⟨hyK, hyU⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨hyA, hyU₂⟩ := Subgroup.mem_inf.mp hyK
  refine MulEquiv.ext fun w => ?_
  have hw : w ∈ commSub (⊤ : Subgroup W) L ⊔ commSub (⊤ : Subgroup W) L₂ := by
    rw [hB.sup]; exact Subgroup.mem_top w
  obtain ⟨u, hu, v, hv, huv⟩ := Subgroup.mem_sup.mp hw
  have hyu : y u = u := mem_centSub.mp hyU u hu
  have hyv : y v = v := mem_centSub.mp hyU₂ v hv
  show y w = w
  calc y w = y (u * v) := by rw [huv]
    _ = y u * y v := map_mul y u v
    _ = u * v := by rw [hyu, hyv]
    _ = w := huv

theorem s16h_e3_Z3NineAAA_transport
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {A L L₂ : Subgroup (MulAut W)} {x : MulAut W}
    (hB : s16h_Z3Blocks A L L₂ x) (hLA : L ≤ A) (hL : Nat.card ↥L = 3)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6)
    (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥)
    (hO2 : ∀ P : Subgroup (MulAut W), P ≤ A → (P.subgroupOf A).Normal → IsPGroup 2 P → P = ⊥)
    (hm : E3.mParam A ≤ 2)
    {t : MulAut W} (htA : t ∈ A) (ht2 : t ^ 2 = 1)
    (htr : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3)
    (htL : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥) {Q : Subgroup (MulAut W)} (hQA : Q ≤ A)
    (hQ : IsElemAbelian 3 Q)
    (hQ9 : 9 * Nat.card ↥(Q ⊓ centSub (commSub (⊤ : Subgroup W) L)) ≤ Nat.card ↥Q)
    {j : MulAut W} (hjA : j ∈ A) (hj2 : j ^ 2 = 1) (hj1 : j ≠ 1)
    (hjU₂ : j ∈ centSub (commSub (⊤ : Subgroup W) L₂))
    (hjL : ∀ l ∈ L, j * l = l * j)
    (hcore : ∀ (N K : Subgroup (coordinateSemilinearGroup 3 OmegaField))
      (hKN : K ≤ N) (hKnorm : (K.subgroupOf N).Normal)
      (hO2 : ∀ P : Subgroup (coordinateSemilinearGroup 3 OmegaField), P ≤ K →
        (P.subgroupOf K).Normal → IsPGroup 2 P → P = ⊥)
      (hZK : ∀ c : OmegaFieldˣ, (SemidirectProduct.inl
        (Matrix.GeneralLinearGroup.scalar (Fin 3) c) : coordinateSemilinearGroup 3 OmegaField) ∈ K)
      {t : coordinateSemilinearGroup 3 OmegaField} (htK : t ∈ K) (ht2 : t ^ 2 = 1)
      (htn : SemidirectProduct.rightHom t ≠ 1)
      {u : Matrix.GeneralLinearGroup (Fin 3) OmegaField}
      (huK : (SemidirectProduct.inl u : coordinateSemilinearGroup 3 OmegaField) ∈ K)
      (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1)
      {Q : Subgroup (coordinateSemilinearGroup 3 OmegaField)} (hQN : Q ≤ N)
      (hQ : IsElemAbelian 3 Q) (hQ9 : 9 ≤ Nat.card ↥Q),
      ∃ P : Subgroup (coordinateSemilinearGroup 3 OmegaField),
        P ≤ K ∧ IsElemAbelian 3 P ∧ 9 ≤ Nat.card ↥P) :
    ∃ P : Subgroup (MulAut W), P ≤ A ⊓ centSub (commSub (⊤ : Subgroup W) L₂) ∧
      IsElemAbelian 3 P ∧ 9 ≤ Nat.card ↥P := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let U : Subgroup W := commSub (⊤ : Subgroup W) L
  let U₂ : Subgroup W := commSub (⊤ : Subgroup W) L₂
  let N : Subgroup (MulAut W) := A ⊓ Subgroup.normalizer (L : Set (MulAut W))
  let K₁ : Subgroup (MulAut W) := A ⊓ centSub U₂
  have hK₁N : K₁ ≤ N := s16h_e3_Z3NineAAA_cent_le_normalizer hB (by simpa only [U] using hrk)
  have hNstab : N ≤ stabSub U := by
    intro n hn
    obtain ⟨hnA, hnN⟩ := Subgroup.mem_inf.mp hn
    exact (hB.stab n hnA (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN)).1
  have hK₁stab : K₁ ≤ stabSub U := fun k hk => hNstab (hK₁N hk)
  obtain ⟨z, hzL, hzord, hLz⟩ :=
    CFSG.GroupTheory.exists_generator_of_card_prime (p := 3) (by norm_num) hL
  have hzN : z ∈ N := ⟨hLA hzL, Subgroup.le_normalizer hzL⟩
  let z' : MulAut U := resHom U ⟨z, hNstab hzN⟩
  have hz'3 : z' ^ 3 = 1 := by
    have hz3' : z ^ 3 = 1 := by
      simpa only [hzord] using pow_orderOf_eq_one z
    have hz3 : (⟨z, hNstab hzN⟩ : ↥(stabSub U)) ^ 3 = 1 := by
      apply (stabSub U).subtype_injective
      simpa [Subgroup.subtype_apply] using hz3'
    show (resHom U ⟨z, hNstab hzN⟩) ^ 3 = 1
    rw [← map_pow, hz3, map_one]
  have hz'ne : z' ≠ 1 := by
    intro hz1
    have hker : (⟨z, hNstab hzN⟩ : ↥(stabSub U)) ∈ (resHom U).ker := by
      rw [MonoidHom.mem_ker]
      simpa only [z'] using hz1
    rw [ker_resHom, Subgroup.mem_subgroupOf] at hker
    have hUle : U ≤ fixV L := by
      intro u hu
      have hzu : z u = u := mem_centSub.mp hker u hu
      rw [hLz, mem_fixV_zpowers_iff_apply]
      exact hzu
    have hUbot : U = ⊥ := by
      rw [← le_bot_iff]
      calc U ≤ U ⊓ fixV L := le_inf le_rfl hUle
        _ = ⊥ := by simpa only [U] using hfix
    have hrkU : rk U = 6 := by simpa only [U] using hrk
    rw [hUbot, rk_bot] at hrkU
    omega
  have hz'ord : orderOf z' = 3 := orderOf_eq_prime hz'3 hz'ne
  have hWU : ∀ u : U, u ^ 2 = 1 := by
    intro u
    apply Subtype.ext
    show (u : W) ^ 2 = 1
    exact hW u
  have hcardU : Nat.card U = 2 ^ 6 := by
    rw [card_eq_two_pow hW U, show rk U = 6 from by simpa only [U] using hrk]
  have hz'fpf : ∀ u : U, z' u = u → u = 1 := by
    intro u hu
    have hzu : z (u : W) = (u : W) := by
      have h1 := congrArg Subtype.val hu
      simp only [z'] at h1
      rwa [resHom_apply] at h1
    have hmem : (u : W) ∈ U ⊓ fixV L := by
      refine Subgroup.mem_inf.mpr ⟨u.2, ?_⟩
      rw [hLz, mem_fixV_zpowers_iff_apply]
      exact hzu
    rw [show U ⊓ fixV L = ⊥ from by simpa only [U] using hfix] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  obtain ⟨e, he⟩ :=
    exists_omega_coordinates_of_order_three_rank_six hWU hcardU z' hz'ord hz'fpf
  have hmem_conj : ∀ a : ↥(stabSub U), (a : MulAut W) ∈ N →
      ∀ y ∈ Subgroup.zpowers z', resHom U a * y * (resHom U a)⁻¹ ∈
        Subgroup.zpowers z' := by
    intro a haN y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have han : (a : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.mem_inf.mp haN).2
    have haz : (a : MulAut W) * z * (a : MulAut W)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp han z).mp hzL
    rw [hLz, Subgroup.mem_zpowers_iff] at haz
    obtain ⟨k, hk⟩ := haz
    have hgen : resHom U a * z' * (resHom U a)⁻¹ ∈ Subgroup.zpowers z' := by
      have hsub : a * ⟨z, hNstab hzN⟩ * a⁻¹ ∈
          Subgroup.zpowers (⟨z, hNstab hzN⟩ : ↥(stabSub U)) := by
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨k, ?_⟩
        apply (stabSub U).subtype_injective
        change z ^ k = (a : MulAut W) * z * (a : MulAut W)⁻¹
        rw [hk]
      have hmap : Subgroup.map (resHom U)
            (Subgroup.zpowers (⟨z, hNstab hzN⟩ : ↥(stabSub U))) =
          Subgroup.zpowers z' := by
        rw [MonoidHom.map_zpowers]
      have hval : resHom U (a * ⟨z, hNstab hzN⟩ * a⁻¹) =
          resHom U a * z' * (resHom U a)⁻¹ := by
        simp only [map_mul, map_inv, z']
      rw [← hval, ← hmap]
      exact Subgroup.mem_map_of_mem _ hsub
    have heq : resHom U a * z' ^ n * (resHom U a)⁻¹
        = (resHom U a * z' * (resHom U a)⁻¹) ^ n := by
      have h1 : (MulAut.conj (resHom U a)) z' = resHom U a * z' * (resHom U a)⁻¹ :=
        MulAut.conj_apply (resHom U a) z'
      calc resHom U a * z' ^ n * (resHom U a)⁻¹
          = (MulAut.conj (resHom U a)) (z' ^ n) := by rw [MulAut.conj_apply]
        _ = ((MulAut.conj (resHom U a)) z') ^ n := map_zpow _ _ _
        _ = (resHom U a * z' * (resHom U a)⁻¹) ^ n := by rw [h1]
    rw [heq]
    exact Subgroup.zpow_mem (Subgroup.zpowers z') hgen n
  have hAN : autSub N U ≤ Subgroup.normalizer (Subgroup.zpowers z' : Set (MulAut U)) := by
    intro φ hφ
    obtain ⟨g, hgN, rfl⟩ := mem_autSub.mp hφ
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hmem_conj g hgN y
    · intro hy
      have h := hmem_conj (g⁻¹) (N.inv_mem hgN) (resHom U g * y * (resHom U g)⁻¹) hy
      simpa [map_inv, mul_assoc] using h
  obtain ⟨ρ, hρinj, hact, hker⟩ :=
    exists_coordinate_semilinear_action_of_normalizes_three
      hWU z' hz'ord e he (autSub N U) hAN
  have hQN : Q ≤ N := by
    intro q hq
    refine ⟨hQA hq, ?_⟩
    change q ∈ Subgroup.normalizer (L : Set (MulAut W))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact (s16h_z3_commute_of_pow_three hB hL (hQA hq) (hQ.2 q hq)).1
  have htdata := s16h_e3_z3_t_data hW hB hL (by simpa only [U] using hrk)
    (by simpa only [U] using hfix) htA ht2 htr htL
  have htU₂ : t ∈ centSub U₂ := htdata.1
  have htinv : ∀ l ∈ L, t * l * t⁻¹ = l⁻¹ := htdata.2
  have htK₁ : t ∈ K₁ := ⟨htA, htU₂⟩
  have htN : t ∈ N := by
    refine ⟨htA, ?_⟩
    change t ∈ Subgroup.normalizer (L : Set (MulAut W))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    ext l
    constructor
    · rintro ⟨l', hl', rfl⟩
      change t * l' * t⁻¹ ∈ L
      rw [htinv l' hl']
      exact L.inv_mem hl'
    · intro hl
      exact ⟨l⁻¹, L.inv_mem hl,
        by change t * l⁻¹ * t⁻¹ = l; rw [htinv (l⁻¹) (L.inv_mem hl), inv_inv]⟩
  have hjN : j ∈ N := by
    refine ⟨hjA, ?_⟩
    change j ∈ Subgroup.normalizer (L : Set (MulAut W))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    ext l
    constructor
    · rintro ⟨l', hl', rfl⟩
      change j * l' * j⁻¹ ∈ L
      rw [hjL l' hl']
      simpa using hl'
    · intro hl
      exact ⟨l, hl, by change j * l * j⁻¹ = l; rw [hjL l hl]; group⟩
  have hjK₁ : j ∈ K₁ := ⟨hjA, hjU₂⟩
  let F : N →* coordinateSemilinearGroup 3 OmegaField :=
    { toFun := fun n => ρ ⟨resHom U ⟨(n : MulAut W), hNstab n.2⟩,
        mem_autSub.mpr ⟨⟨(n : MulAut W), hNstab n.2⟩, n.2, rfl⟩⟩
      map_one' := by
        have h : (⟨resHom U ⟨((1 : N) : MulAut W), hNstab (1 : N).2⟩,
            mem_autSub.mpr ⟨⟨((1 : N) : MulAut W), hNstab (1 : N).2⟩,
              (1 : N).2, rfl⟩⟩ : autSub N U) = 1 := by
          apply Subtype.ext
          show resHom U ⟨((1 : N) : MulAut W), hNstab (1 : N).2⟩ = 1
          rw [show (⟨((1 : N) : MulAut W), hNstab (1 : N).2⟩ :
            ↥(stabSub U)) = 1 from Subtype.ext rfl, map_one]
        rw [h, map_one]
      map_mul' := by
        intro a b
        have h : (⟨resHom U ⟨((a * b : N) : MulAut W), hNstab (a * b).2⟩,
            mem_autSub.mpr ⟨⟨((a * b : N) : MulAut W), hNstab (a * b).2⟩,
              (a * b).2, rfl⟩⟩ : autSub N U) =
            ⟨resHom U ⟨(a : MulAut W), hNstab a.2⟩,
              mem_autSub.mpr ⟨⟨(a : MulAut W), hNstab a.2⟩, a.2, rfl⟩⟩ *
            ⟨resHom U ⟨(b : MulAut W), hNstab b.2⟩,
              mem_autSub.mpr ⟨⟨(b : MulAut W), hNstab b.2⟩, b.2, rfl⟩⟩ := by
          apply Subtype.ext
          show resHom U ⟨((a * b : N) : MulAut W), hNstab (a * b).2⟩ =
            resHom U ⟨(a : MulAut W), hNstab a.2⟩ * resHom U ⟨(b : MulAut W), hNstab b.2⟩
          rw [show (⟨((a * b : N) : MulAut W), hNstab (a * b).2⟩ : ↥(stabSub U)) =
              ⟨(a : MulAut W), hNstab a.2⟩ * ⟨(b : MulAut W), hNstab b.2⟩ from
            Subtype.ext rfl, map_mul]
        rw [h, map_mul ρ] }
  let Nmat : Subgroup (coordinateSemilinearGroup 3 OmegaField) := F.range
  let Kmat : Subgroup (coordinateSemilinearGroup 3 OmegaField) := (K₁.subgroupOf N).map F
  let Qmat : Subgroup (coordinateSemilinearGroup 3 OmegaField) := (Q.subgroupOf N).map F
  let zcomm : ↥(stabSub U) := ⟨z, hNstab hzN⟩
  let tcomm : ↥(stabSub U) := ⟨t, hNstab htN⟩
  let jcomm : ↥(stabSub U) := ⟨j, hNstab hjN⟩
  let zaut : autSub N U := ⟨z', mem_autSub.mpr ⟨zcomm, hzN, rfl⟩⟩
  let taut : autSub N U := ⟨resHom U tcomm, mem_autSub.mpr ⟨tcomm, htN, rfl⟩⟩
  let jaut : autSub N U := ⟨resHom U jcomm, mem_autSub.mpr ⟨jcomm, hjN, rfl⟩⟩
  let tmat : coordinateSemilinearGroup 3 OmegaField := F ⟨t, htN⟩
  have htmat : tmat = ρ taut := by simp [F, tmat, taut, tcomm]
  have hQN' : Qmat ≤ Nmat := Subgroup.map_le_range F (Q.subgroupOf N)
  have hKN : Kmat ≤ Nmat := Subgroup.map_le_range F (K₁.subgroupOf N)
  have hKmat_t : tmat ∈ Kmat :=
    Subgroup.mem_map.mpr ⟨⟨t, htN⟩, htK₁, rfl⟩
  have hKmat_j : F ⟨j, hjN⟩ ∈ Kmat :=
    Subgroup.mem_map.mpr ⟨⟨j, hjN⟩, hjK₁, rfl⟩
  have hjautC : (jaut : MulAut U) * z' = z' * (jaut : MulAut U) := by
    have hcomm : jcomm * zcomm = zcomm * jcomm := by
      apply Subtype.ext
      show j * z = z * j
      exact hjL z hzL
    calc resHom U jcomm * z' = resHom U (jcomm * zcomm) := by
          change resHom U jcomm * resHom U zcomm = resHom U (jcomm * zcomm)
          rw [← map_mul]
      _ = resHom U (zcomm * jcomm) := by rw [hcomm]
      _ = z' * resHom U jcomm := by
          change resHom U (zcomm * jcomm) = resHom U zcomm * resHom U jcomm
          rw [map_mul]
  have hjautker : jaut ∈ (SemidirectProduct.rightHom.comp ρ).ker := by
    rw [hker]
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr hjautC)
  let u : Matrix.GeneralLinearGroup (Fin 3) OmegaField := (ρ jaut).left
  have hρjaut : ρ jaut = SemidirectProduct.inl u := by
    have hright : (ρ jaut).right = 1 := by
      have := MonoidHom.mem_ker.mp hjautker
      simpa [MonoidHom.comp_apply] using this
    rw [← SemidirectProduct.inl_left_mul_inr_right (ρ jaut), hright, map_one, mul_one]
  have hjF_u : F ⟨j, hjN⟩ = SemidirectProduct.inl u := by
    have h1 : F ⟨j, hjN⟩ = ρ jaut := congrArg ρ (by apply Subtype.ext; rfl)
    rw [h1, hρjaut]
  have huK : (SemidirectProduct.inl u : coordinateSemilinearGroup 3 OmegaField) ∈ Kmat := by
    rw [← hjF_u]
    exact hKmat_j
  have hj_centU_bot : j ∈ centSub U → j = 1 := by
    intro hjU
    have hmem : j ∈ (A ⊓ centSub U₂) ⊓ centSub U := ⟨⟨hjA, hjU₂⟩, hjU⟩
    rw [s16h_e3_Z3NineAAA_cent_inf_cent_bot hB] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hu2 : u ^ 2 = 1 := by
    have hjaut2 : jaut ^ 2 = 1 := by
      apply Subtype.ext
      show resHom U jcomm ^ 2 = 1
      rw [← map_pow, show jcomm ^ 2 = (1 : ↥(stabSub U)) from by
        apply Subtype.ext; show j ^ 2 = 1; exact hj2, map_one]
    have h2 : ((SemidirectProduct.inl u : coordinateSemilinearGroup 3 OmegaField)) ^ 2 = 1 := by
      calc ((SemidirectProduct.inl u : coordinateSemilinearGroup 3 OmegaField)) ^ 2 =
            (ρ jaut) ^ 2 := by rw [hρjaut]
        _ = ρ (jaut ^ 2) := (map_pow ρ jaut 2).symm
        _ = 1 := by rw [hjaut2, map_one]
    exact SemidirectProduct.inl_injective (by simpa [map_pow] using h2)
  have hu1 : u ≠ 1 := by
    intro hu1
    have hjaut1 : jaut = 1 := by
      apply hρinj
      rw [hρjaut, hu1]
      simp
    have hjU : j ∈ centSub U := by
      rw [mem_centSub]
      intro v hv
      have : (jaut : MulAut U) = 1 := by rw [hjaut1]; rfl
      have h := congrArg (fun φ : MulAut U => ((φ ⟨v, hv⟩ : U) : W)) this
      simpa [jaut, resHom_apply] using h
    exact hj1 (hj_centU_bot hjU)
  have ht2mat : tmat ^ 2 = 1 := by
    rw [htmat]
    calc (ρ taut) ^ 2 = ρ (taut ^ 2) := (map_pow ρ taut 2).symm
      _ = 1 := by
        have : taut ^ 2 = 1 := by
          apply Subtype.ext
          show resHom U tcomm ^ 2 = 1
          rw [← map_pow, show tcomm ^ 2 = (1 : ↥(stabSub U)) from by
            apply Subtype.ext; show t ^ 2 = 1; exact ht2, map_one]
        rw [this, map_one]
  have hK₁normal : (K₁.subgroupOf N).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnA, hnU₂⟩ := Subgroup.mem_inf.mp hn
    have hgA : (g : MulAut W) ∈ A := (Subgroup.mem_inf.mp g.2).1
    have hgN : (g : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.mem_inf.mp g.2).2
    have hgstab := hB.stab (g : MulAut W) hgA
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN)
    refine ⟨A.mul_mem (A.mul_mem hgA hnA) (A.inv_mem hgA), ?_⟩
    change ((g : MulAut W) * (n : MulAut W) * (g : MulAut W)⁻¹) ∈ centSub U₂
    rw [mem_centSub]
    intro v hv
    have hnv : (g : MulAut W)⁻¹ v ∈ U₂ :=
      (mem_stabSub.mp hgstab.2 ((g : MulAut W)⁻¹ v)).1 (by simpa using hv)
    have hfix : (n : MulAut W) ((g : MulAut W)⁻¹ v) = (g : MulAut W)⁻¹ v :=
      mem_centSub.mp hnU₂ _ hnv
    change ((g : MulAut W) * (n : MulAut W) * (g : MulAut W)⁻¹) v = v
    rw [MulAut.mul_apply, MulAut.mul_apply, hfix, MulAut.apply_inv_self]
  have hKnorm : (Kmat.subgroupOf Nmat).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨n, hn, hnF⟩ := Subgroup.mem_map.mp hx
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp y.2
    refine Subgroup.mem_map.mpr ⟨m * n * m⁻¹, hK₁normal.conj_mem n hn m, ?_⟩
    change F (m * n * m⁻¹) = (y : coordinateSemilinearGroup 3 OmegaField) *
      (x : coordinateSemilinearGroup 3 OmegaField) *
      (y : coordinateSemilinearGroup 3 OmegaField)⁻¹
    rw [map_mul, map_mul, map_inv, hm, hnF]
  let g : ↥(K₁.subgroupOf N) →* coordinateSemilinearGroup 3 OmegaField :=
    F.comp (K₁.subgroupOf N).subtype
  have hg_range : g.range = Kmat := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  have hF_one_cent : ∀ x : ↥(K₁.subgroupOf N), F x.1 = 1 →
      (x.1.1 : MulAut W) ∈ centSub U := by
    intro x hx
    have h2 : (⟨resHom U ⟨(x.1.1 : MulAut W), hNstab x.1.2⟩,
        mem_autSub.mpr ⟨⟨(x.1.1 : MulAut W), hNstab x.1.2⟩, x.1.2, rfl⟩⟩ :
          autSub N U) = 1 := by
      apply hρinj
      rw [map_one]
      have hx' : ρ ⟨resHom U ⟨(x.1.1 : MulAut W), hNstab x.1.2⟩,
          mem_autSub.mpr ⟨⟨(x.1.1 : MulAut W), hNstab x.1.2⟩, x.1.2, rfl⟩⟩ = 1 := hx
      rw [hx']
    have h3 : resHom U ⟨(x.1.1 : MulAut W), hNstab x.1.2⟩ = 1 :=
      congrArg Subtype.val h2
    rw [mem_centSub]
    intro v hv
    have := congrArg (fun φ : MulAut U => ((φ ⟨v, hv⟩ : U) : W)) h3
    simpa [resHom_apply] using this
  have hg_inj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxcent : (x.1.1 : MulAut W) ∈ centSub U := hF_one_cent x hx
    have hxbot : (x.1.1 : MulAut W) ∈ (A ⊓ centSub U₂) ⊓ centSub U :=
      ⟨(Subgroup.mem_subgroupOf.mp x.2), hxcent⟩
    rw [s16h_e3_Z3NineAAA_cent_inf_cent_bot hB] at hxbot
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hxbot
  have hcoreO2 : ∀ P : Subgroup (coordinateSemilinearGroup 3 OmegaField), P ≤ Kmat →
      (P.subgroupOf Kmat).Normal → IsPGroup 2 P → P = ⊥ := by
    intro P hPK hPN hP2
    exact s16h_e3_Z3NineAAAA_Kmat_o2_bot hB hLA hL hrk hO2 hK₁N F
      (fun a b h => hg_inj (by simpa [g] using h)) P hPK hPN hP2
  have hZK : ∀ c : OmegaFieldˣ, (SemidirectProduct.inl
      (Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
        coordinateSemilinearGroup 3 OmegaField) ∈ Kmat := by
    have homega0 : CFSG.LinearAlgebra.omega ≠ 0 := by
      intro h0
      have h2 := omega_sq
      rw [h0] at h2
      simp at h2
    let omegaUnit : OmegaFieldˣ := Units.mk0 CFSG.LinearAlgebra.omega homega0
    have homegaUnit_val : (omegaUnit : OmegaField) = CFSG.LinearAlgebra.omega := rfl
    have homega3 : CFSG.LinearAlgebra.omega ^ 3 = 1 := by
      have h2 : CFSG.LinearAlgebra.omega + CFSG.LinearAlgebra.omega = 0 := by
        rw [← two_mul, omegaField_two_eq_zero, zero_mul]
      calc CFSG.LinearAlgebra.omega ^ 3 = CFSG.LinearAlgebra.omega ^ 2 *
            CFSG.LinearAlgebra.omega := by ring
        _ = (CFSG.LinearAlgebra.omega + 1) * CFSG.LinearAlgebra.omega := by rw [omega_sq]
        _ = CFSG.LinearAlgebra.omega ^ 2 + CFSG.LinearAlgebra.omega := by ring
        _ = (CFSG.LinearAlgebra.omega + 1) + CFSG.LinearAlgebra.omega := by rw [omega_sq]
        _ = 1 + (CFSG.LinearAlgebra.omega + CFSG.LinearAlgebra.omega) := by ring
        _ = 1 := by rw [h2, add_zero]
    have homegaUnit3 : omegaUnit ^ 3 = 1 := by
      apply Units.ext
      simp [homegaUnit_val, homega3]
    have homega1 : CFSG.LinearAlgebra.omega ≠ 1 := by
      intro h1
      have h2 : (1 : OmegaField) = 1 + 1 := by simpa [h1] using omega_sq
      rw [one_add_one_eq_two, omegaField_two_eq_zero] at h2
      exact one_ne_zero h2
    have homegaUnit1 : omegaUnit ≠ 1 := by
      intro h
      apply homega1
      have := congrArg (fun u : OmegaFieldˣ => (u : OmegaField)) h
      simpa [homegaUnit_val] using this
    have hcard : Nat.card OmegaFieldˣ = 3 := by
      rw [Nat.card_units, s16h_e3_z3_card_omegaField_eq_four]
    have hord : orderOf omegaUnit = 3 := orderOf_eq_prime homegaUnit3 homegaUnit1
    have htop : Subgroup.zpowers omegaUnit = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, hcard])
    have hzaut : ρ zaut = SemidirectProduct.inl
        (Matrix.GeneralLinearGroup.scalar (Fin 3) omegaUnit) := by
      apply coordinateSemilinearHom_injective (d := 3) (K := OmegaField) (by norm_num)
      apply congrArg Multiplicative.ofAdd
      ext v
      have hlhs : coordinateSemilinearMap (ρ zaut) v = CFSG.LinearAlgebra.omega • v := by
        let w : U := e.symm (Multiplicative.ofAdd v)
        have hw : Multiplicative.toAdd (e w) = v := by simp [w]
        rw [← hw, ← hact zaut w, he w]
      rw [hlhs, coordinateSemilinearMap_inl,
        CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer.matrixLinearEquiv_scalar,
        homegaUnit_val]
    have hFz : F ⟨z, hzN⟩ = SemidirectProduct.inl
        (Matrix.GeneralLinearGroup.scalar (Fin 3) omegaUnit) := by
      rw [show F ⟨z, hzN⟩ = ρ zaut from rfl, hzaut]
    intro c
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (by rw [htop]; exact Subgroup.mem_top c)
    rw [← hk]
    have hzU₂ : z ∈ centSub U₂ := by simpa only [U₂] using hB.cent₁ hzL
    have hzK₁ : z ∈ K₁ := ⟨hLA hzL, hzU₂⟩
    have hzmem : (⟨z, hzN⟩ : N) ∈ K₁.subgroupOf N :=
      Subgroup.mem_subgroupOf.mpr hzK₁
    have hzpmem : (⟨z, hzN⟩ : N) ^ k ∈ K₁.subgroupOf N :=
      (K₁.subgroupOf N).zpow_mem hzmem k
    have hFmem : F ((⟨z, hzN⟩ : N) ^ k) ∈ Kmat :=
      Subgroup.mem_map.mpr ⟨(⟨z, hzN⟩ : N) ^ k, hzpmem, rfl⟩
    have hgoal : (SemidirectProduct.inl
        (Matrix.GeneralLinearGroup.scalar (Fin 3) (omegaUnit ^ k)) :
          coordinateSemilinearGroup 3 OmegaField) = F ((⟨z, hzN⟩ : N) ^ k) := by
      calc (SemidirectProduct.inl
            (Matrix.GeneralLinearGroup.scalar (Fin 3) (omegaUnit ^ k)) :
              coordinateSemilinearGroup 3 OmegaField)
          = SemidirectProduct.inl
              ((Matrix.GeneralLinearGroup.scalar (Fin 3) omegaUnit) ^ k) := by
            rw [map_zpow]
        _ = (SemidirectProduct.inl
              (Matrix.GeneralLinearGroup.scalar (Fin 3) omegaUnit)) ^ k := by
            rw [map_zpow]
        _ = (F ⟨z, hzN⟩) ^ k := by rw [hFz]
        _ = F ((⟨z, hzN⟩ : N) ^ k) := (map_zpow F ⟨z, hzN⟩ k).symm
    rw [hgoal]
    exact hFmem
  have htaut_conj : (taut : MulAut U) * z' * (taut : MulAut U)⁻¹ = z' ^ 2 := by
    have hz3 : z ^ 3 = 1 := by simpa only [hzord] using pow_orderOf_eq_one z
    have hz2 : z ^ 2 = z⁻¹ := by
      calc z ^ 2 = z⁻¹ * z ^ 3 := by group
        _ = z⁻¹ := by rw [hz3, mul_one]
    have htinv2 : tcomm * zcomm * tcomm⁻¹ = zcomm ^ 2 := by
      apply Subtype.ext
      show t * z * t⁻¹ = z ^ 2
      rw [htinv z hzL, ← hz2]
    calc (taut : MulAut U) * z' * (taut : MulAut U)⁻¹
        = resHom U (tcomm * zcomm * tcomm⁻¹) := by
          change resHom U tcomm * resHom U zcomm * (resHom U tcomm)⁻¹ =
            resHom U (tcomm * zcomm * tcomm⁻¹)
          rw [← map_mul, ← map_inv, ← map_mul]
      _ = resHom U (zcomm ^ 2) := by rw [htinv2]
      _ = z' ^ 2 := by rw [map_pow]
  have htn : SemidirectProduct.rightHom tmat ≠ 1 := by
    intro hright
    have htautker : taut ∈ (SemidirectProduct.rightHom.comp ρ).ker := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← htmat]
      exact hright
    rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at htautker
    have h1 : (taut : MulAut U) * z' * (taut : MulAut U)⁻¹ = z' := by
      rw [htautker]; group
    have hz_eq : z' = z' ^ 2 := by
      rw [← htaut_conj, h1]
    have hz1 : z' = 1 := by
      have := congrArg (fun x => z'⁻¹ * x) hz_eq
      simpa [pow_two, eq_comm] using this
    exact hz'ne hz1
  have hQ'mat : IsElemAbelian 3 Qmat := (hQ.subgroupOf N).map F
  have hQ9'mat : 9 ≤ Nat.card ↥Qmat := by
    have hFker : F.ker = (centSub U).subgroupOf N := by
      ext n
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_centSub]
      constructor
      · intro hn u hu
        have h1 : (⟨resHom U ⟨(n : MulAut W), hNstab n.2⟩,
            mem_autSub.mpr ⟨⟨(n : MulAut W), hNstab n.2⟩, n.2, rfl⟩⟩ :
              autSub N U) = 1 := by
          apply hρinj
          rw [map_one]
          simpa [F] using hn
        have h2 : resHom U ⟨(n : MulAut W), hNstab n.2⟩ = 1 :=
          congrArg Subtype.val h1
        have h3 : (⟨(n : MulAut W), hNstab n.2⟩ : ↥(stabSub U)) ∈ (resHom U).ker := by
          rw [MonoidHom.mem_ker]
          exact h2
        rw [ker_resHom, Subgroup.mem_subgroupOf] at h3
        exact h3 u hu
      · intro hn
        have h3 : (⟨(n : MulAut W), hNstab n.2⟩ : ↥(stabSub U)) ∈
            (centSub U).subgroupOf (stabSub U) :=
          Subgroup.mem_subgroupOf.mpr hn
        rw [← ker_resHom, MonoidHom.mem_ker] at h3
        have h4 : (⟨resHom U ⟨(n : MulAut W), hNstab n.2⟩,
            mem_autSub.mpr ⟨⟨(n : MulAut W), hNstab n.2⟩, n.2, rfl⟩⟩ :
              autSub N U) = 1 := Subtype.ext (by simpa using h3)
        show ρ ⟨resHom U ⟨(n : MulAut W), hNstab n.2⟩,
          mem_autSub.mpr ⟨⟨(n : MulAut W), hNstab n.2⟩, n.2, rfl⟩⟩ = 1
        rw [h4, map_one]
    have hcardQ : Nat.card ↥(Q.subgroupOf N) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv
    have hcardK : Nat.card ↥((Q.subgroupOf N) ⊓ F.ker) =
        Nat.card ↥(Q ⊓ centSub U) := by
      have h : (Q.subgroupOf N) ⊓ (centSub U).subgroupOf N =
          (Q ⊓ centSub U).subgroupOf N := by
        ext x
        simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      rw [hFker, h]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hQN)).toEquiv
    have hprod := B1More.card_map_mul_card_inf_ker (Q.subgroupOf N) F
    rw [show (Q.subgroupOf N).map F = Qmat from rfl, hcardK, hcardQ] at hprod
    have hp : 0 < Nat.card ↥(Q ⊓ centSub U) := card_subgroup_pos _
    refine Nat.le_of_mul_le_mul_right ?_ hp
    rw [hprod]
    exact hQ9
  obtain ⟨Pmat, hPmatK, hPmatE, hPmat9⟩ :=
    hcore Nmat Kmat hKN hKnorm hcoreO2 hZK
      (t := tmat) hKmat_t ht2mat htn
      (u := u) huK hu2 hu1
      (Q := Qmat) hQN' hQ'mat hQ9'mat
  let embed : ↥(K₁.subgroupOf N) →* MulAut W :=
    N.subtype.comp (K₁.subgroupOf N).subtype
  have hembed_inj : Function.Injective embed :=
    N.subtype_injective.comp (K₁.subgroupOf N).subtype_injective
  refine ⟨(Pmat.comap g).map embed, ?_, ?_, ?_⟩
  · rintro p ⟨x, -, rfl⟩
    exact Subgroup.mem_subgroupOf.mp x.2
  · exact (hPmatE.comap (f := g) hg_inj).map embed
  · have h1 : Nat.card ↥((Pmat.comap g).map embed) = Nat.card ↥(Pmat.comap g) :=
      Subgroup.card_map_of_injective (f := embed) (K := Pmat.comap g) hembed_inj
    have h2 : Nat.card ↥(Pmat.comap g) = Nat.card ↥Pmat := by
      have h := Subgroup.card_map_of_injective (f := g) (K := Pmat.comap g) hg_inj
      rw [Subgroup.map_comap_eq_self (by rw [hg_range]; exact hPmatK)] at h
      exact h.symm
    rw [h1, h2]
    exact hPmat9

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
