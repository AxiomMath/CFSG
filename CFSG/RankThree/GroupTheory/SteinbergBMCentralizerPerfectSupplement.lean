module

public import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniNormalizerTwoCore
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowContainment
public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG.RankThree.LocalRank
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem le_normalizer_inSubgroup_of_characteristic {F : ∀ (K : Type _) [Group K], Subgroup K}
    {L : Subgroup G} (hF : (F L).Characteristic) :
    normalizer (L : Set G) ≤ normalizer ((CFSG.inSubgroup F L : Subgroup G) : Set G) := by
  refine le_normalizer_of_forall_conj_mem fun g hg x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  set σ : MulAut L := L.normalizerMonoidHom ⟨g, hg⟩ with hσ
  have hmap := (characteristic_iff_map_eq.mp hF) σ
  have hσy : σ y ∈ F L := by
    rw [← hmap]
    exact mem_map_of_mem _ hy
  exact ⟨σ y, hσy, rfl⟩

theorem exists_centralizer_inv_mul_mem [Finite G] {B M N : Subgroup G}
    (hBM : B ≤ normalizer (M : Set G)) (hBN : B ≤ normalizer (N : Set G))
    (hMN : M ≤ normalizer (N : Set G)) (hNs : Group.IsSolvable N)
    (hcop : Nat.Coprime (Nat.card B) (Nat.card N)) (hMB : ⁅M, B⁆ ≤ N) :
    ∀ m ∈ M, ∃ c ∈ M ⊓ centralizer (B : Set G), c⁻¹ * m ∈ N := by
  intro m hm
  let : MulDistribMulAction B M := MulDistribMulAction.compHom M (Subgroup.inclusion hBM)
  have hsmul : ∀ (b : B) (x : M), ((b • x : M) : G) = b * x * (b : G)⁻¹ := fun _ _ => rfl
  set N₀ := N.subgroupOf M with hN₀
  have : N₀.Normal := ⟨fun n hn g => (mem_normalizer_iff.mp (hMN g.2) n).mp hn⟩
  have hNinv : CFSG.IsInvariant B M N₀ := ⟨fun b x => by
    rw [hN₀, mem_subgroupOf, mem_subgroupOf, hsmul]
    exact mem_normalizer_iff.mp (hBN b.2) x⟩
  let f : N₀ →* N := MonoidHom.mk' (fun x => ⟨((x : M) : G), x.2⟩) fun _ _ => rfl
  have hf : Function.Injective f := fun x y h => by
    have h' := congrArg (fun z : N => (z : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hN₀s : Group.IsSolvable N₀ := Group.isSolvable_of_isSolvable_injective hf
  have hcop₀ : Nat.Coprime (Nat.card B) (Nat.card N₀) :=
    Nat.Coprime.coprime_dvd_right (card_dvd_of_injective f hf) hcop
  have hlift := CFSG.SolvableHall.coprime_solvable_kernel_fixed_point_lifting N₀ hNinv hN₀s hcop₀
  let : MulDistribMulAction B (M ⧸ N₀) :=
    CFSG.quotientMulDistribMulAction (A := B) (G := M) N₀ hNinv
  let : MulAction.QuotientAction B N₀ := CFSG.quotientAction_of_isInvariant (A := B) N₀ hNinv
  have hfix : ((⟨m, hm⟩ : M) : M ⧸ N₀) ∈ CFSG.fixedPointSubgroup B (M ⧸ N₀) := by
    intro b
    rw [MulAction.Quotient.smul_coe (H := N₀) b ⟨m, hm⟩, QuotientGroup.eq]
    show (((b • (⟨m, hm⟩ : M))⁻¹ * ⟨m, hm⟩ : M) : G) ∈ N
    rw [coe_mul, coe_inv, hsmul]
    have h := commutator_mem_commutator b.2 (M.inv_mem hm)
    rw [commutator_comm] at h
    have h' := hMB h
    rw [commutatorElement_def, inv_inv] at h'
    simpa [mul_assoc] using h'
  rw [hlift] at hfix
  obtain ⟨c, hc, hcm⟩ := hfix
  refine ⟨c, ⟨c.2, mem_centralizer_iff.mpr fun b hb => ?_⟩, ?_⟩
  · have h := congrArg Subtype.val (hc ⟨b, hb⟩)
    rw [hsmul] at h
    calc b * (c : G) = b * c * b⁻¹ * b := by group
      _ = c * b := by rw [h]
  · have := QuotientGroup.eq.mp hcm
    exact this

theorem coprime_two_commutator_centralizer_perfect_supplement [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {B L R : Subgroup G} (hB : IsPGroup p B) (hL : ⁅L, L⁆ = L)
    (hBL : B ≤ normalizer (L : Set G))
    (hLB : ⁅L, B⁆ ≤ CFSG.inSubgroup (aschbacherSolvableCore p) L) (hR2 : IsPGroup 2 R)
    (hBR : B ≤ normalizer (R : Set G)) (hRB : ⁅R, B⁆ = R) (hRL : R ≤ normalizer (L : Set G))
    (hRLθ : ⁅R, L⁆ ≤ CFSG.inSubgroup (aschbacherSolvableCore p) L)
    (hBcent : ∀ T : Subgroup G, T ≤ CFSG.inSubgroup (aschbacherSolvableCore p) L →
      IsPGroup 2 T → B ≤ normalizer (T : Set G) → T ≤ centralizer (B : Set G)) :
    let K := CFSG.inSubgroup CFSG.perfectResidual
      (L ⊓ centralizer ((R ⊔ B : Subgroup G) : Set G))
    ⁅K, K⁆ = K ∧ K ≤ centralizer (R : Set G) ∧ K ≤ centralizer (B : Set G) ∧
      (L : Set G) = (CFSG.inSubgroup (aschbacherSolvableCore p) L : Set G) * (K : Set G) := by
  intro K
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.inSubgroup (aschbacherSolvableCore p) L with hNdef
  obtain ⟨hθs, hθc, hθp, -⟩ := solvable_prime_complement_core_characterization (H := L) hp
  have hNL : N ≤ L := map_subtype_le _
  have hNnorm : normalizer (L : Set G) ≤ normalizer (N : Set G) :=
    le_normalizer_inSubgroup_of_characteristic hθc
  have hLN : L ≤ normalizer (N : Set G) := le_normalizer.trans hNnorm
  have hBN : B ≤ normalizer (N : Set G) := hBL.trans hNnorm
  have hRN : R ≤ normalizer (N : Set G) := hRL.trans hNnorm
  have hNs : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective
      (f := ((aschbacherSolvableCore p L).equivMapOfInjective L.subtype
        L.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _)
  have hNp : ¬ p ∣ Nat.card N := by
    rw [hNdef, CFSG.inSubgroup, card_map_of_injective L.subtype_injective]
    exact hθp
  set D := N ⊔ R with hDdef
  have hDcoeNR : (D : Set G) = (N : Set G) * (R : Set G) :=
    coe_mul_of_right_le_normalizer_left N R hRN
  have hDcoeRN : (D : Set G) = (R : Set G) * (N : Set G) := by
    rw [hDdef, sup_comm]
    exact coe_mul_of_left_le_normalizer_right R N hRN
  have hDdecNR : ∀ x ∈ D, ∃ n ∈ N, ∃ r ∈ R, n * r = x := fun x hx => by
    have hx' : x ∈ (D : Set G) := hx
    rw [hDcoeNR] at hx'
    obtain ⟨n, hn, r, hr, rfl⟩ := hx'
    exact ⟨n, hn, r, hr, rfl⟩
  have hDdecRN : ∀ x ∈ D, ∃ r ∈ R, ∃ n ∈ N, r * n = x := fun x hx => by
    have hx' : x ∈ (D : Set G) := hx
    rw [hDcoeRN] at hx'
    obtain ⟨r, hr, n, hn, rfl⟩ := hx'
    exact ⟨r, hr, n, hn, rfl⟩
  obtain ⟨-, hDp⟩ := isSolvable_and_not_dvd_of_mul_two_group hp hp2 le_sup_left
    (sup_le le_normalizer hRN) hR2 le_sup_right hDdecNR hNs hNp
  have hBD : B ≤ normalizer (D : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun b hb x hx => ?_
    obtain ⟨n, hn, r, hr, rfl⟩ := hDdecNR x hx
    have e : b * (n * r) * b⁻¹ = (b * n * b⁻¹) * (b * r * b⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp (hBN hb) n).mp hn))
      (mem_sup_right ((mem_normalizer_iff.mp (hBR hb) r).mp hr))
  have hLD : L ≤ normalizer (D : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun l hl x hx => ?_
    obtain ⟨n, hn, r, hr, rfl⟩ := hDdecNR x hx
    have hlr : ⁅l, r⁆ ∈ N := by
      have h := N.inv_mem (hRLθ (commutator_mem_commutator hr hl))
      rwa [commutatorElement_inv] at h
    have e : l * (n * r) * l⁻¹ = (l * n * l⁻¹) * ⁅l, r⁆ * r := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mul_mem (mem_sup_left ((mem_normalizer_iff.mp (hLN hl) n).mp hn))
      (mem_sup_left hlr)) (mem_sup_right hr)
  let : MulDistribMulAction B D := MulDistribMulAction.compHom D (Subgroup.inclusion hBD)
  have hsmulD : ∀ (b : B) (x : D), ((b • x : D) : G) = b * x * (b : G)⁻¹ := fun _ _ => rfl
  have hR' : IsPGroup 2 (R.subgroupOf D) :=
    hR2.of_equiv (subgroupOfEquivOfLe (le_sup_right : R ≤ D)).symm
  have hR'inv : ∀ b : B, ∀ x ∈ R.subgroupOf D, b • x ∈ R.subgroupOf D := fun b x hx => by
    rw [mem_subgroupOf, hsmulD]
    exact (mem_normalizer_iff.mp (hBR b.2) x).mp hx
  obtain ⟨P₀, hRP₀, hP₀⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing
    (ActorType := B) (GroupType := D) p 2 hp Nat.prime_two hB
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hDp) (R.subgroupOf D) hR' hR'inv
  have hP₀inv : ∀ b : B, ∀ x ∈ (P₀ : Subgroup D), b • x ∈ (P₀ : Subgroup D) := by
    intro b x hx
    have heq : b • (P₀ : Subgroup D) = (P₀ : Subgroup D) := by
      rw [← Sylow.pointwise_smul_def, hP₀ b]
    rw [← heq]
    exact Subgroup.smul_mem_pointwise_smul x b _ hx
  set P := (P₀ : Subgroup D).map D.subtype with hPdef
  have hPD : P ≤ D := map_subtype_le _
  have hP2 : IsPGroup 2 P := P₀.isPGroup'.map D.subtype
  have hRP : R ≤ P := fun r hr => ⟨⟨r, (le_sup_right : R ≤ D) hr⟩, hRP₀ hr, rfl⟩
  have hBP : B ≤ normalizer (P : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun b hb x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨(⟨b, hb⟩ : B) • y, hP₀inv ⟨b, hb⟩ y hy, rfl⟩
  set T := P ⊓ N with hTdef
  have hTB : T ≤ centralizer (B : Set G) := hBcent T inf_le_right (hP2.to_le inf_le_left)
    (le_normalizer_of_forall_conj_mem fun b hb x hx =>
      ⟨(mem_normalizer_iff.mp (hBP hb) x).mp hx.1, (mem_normalizer_iff.mp (hBN hb) x).mp hx.2⟩)
  have hPB : ⁅P, B⁆ = R := by
    refine le_antisymm ?_ (hRB ▸ commutator_mono hRP le_rfl)
    rw [commutator_le]
    intro u hu b hb
    obtain ⟨r, hr, n, hn, rfl⟩ := hDdecRN u (hPD hu)
    have hnP : n ∈ P := by
      have e : n = r⁻¹ * (r * n) := by group
      rw [e]
      exact P.mul_mem (P.inv_mem (hRP hr)) hu
    have hnb : n * b = b * n := (mem_centralizer_iff.mp (hTB ⟨hnP, hn⟩) b hb).symm
    have e : ⁅r * n, b⁆ = ⁅r, b⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc r * n * b * (r * n)⁻¹ * b⁻¹ = r * (n * b) * n⁻¹ * r⁻¹ * b⁻¹ := by group
        _ = r * (b * n) * n⁻¹ * r⁻¹ * b⁻¹ := by rw [hnb]
        _ = r * b * r⁻¹ * b⁻¹ := by group
    rw [e, ← hRB]
    exact commutator_mem_commutator hr hb
  set M := L ⊓ normalizer (P : Set G) with hMdef
  have hLM : ∀ l ∈ L, ∃ n ∈ N, n * l ∈ M := by
    intro l hl
    obtain ⟨d, hd, hdl⟩ := exists_mul_mem_normalizer_sylow P₀ (hLD hl)
    obtain ⟨r, hr, n, hn, rfl⟩ := hDdecRN d hd
    refine ⟨n, hn, L.mul_mem (hNL hn) hl, ?_⟩
    have hr' : r⁻¹ ∈ normalizer (P : Set G) := le_normalizer (P.inv_mem (hRP hr))
    have h := mul_mem hr' hdl
    simpa [mul_assoc] using h
  have hBM : B ≤ normalizer (M : Set G) := le_normalizer_of_forall_conj_mem fun b hb x hx =>
    ⟨(mem_normalizer_iff.mp (hBL hb) x).mp hx.1, (normalizer (P : Set G)).mul_mem
      ((normalizer (P : Set G)).mul_mem (hBP hb) hx.2) ((normalizer (P : Set G)).inv_mem (hBP hb))⟩
  have hcopBN : Nat.Coprime (Nat.card B) (Nat.card N) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB
    rw [hk]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hNp)
  have hfixlift := exists_centralizer_inv_mul_mem hBM hBN (inf_le_left.trans hLN) hNs hcopBN
    ((commutator_mono inf_le_left le_rfl).trans hLB)
  set CMB := M ⊓ centralizer (B : Set G) with hCMBdef
  have hCMBL : CMB ≤ L := inf_le_left.trans inf_le_left
  have hLNC : ∀ l ∈ L, ∃ n ∈ N, ∃ c ∈ CMB, n * c = l := by
    intro l hl
    obtain ⟨n₁, hn₁, hm⟩ := hLM l hl
    obtain ⟨c, hc, hcn⟩ := hfixlift _ hm
    refine ⟨n₁⁻¹ * (c * (c⁻¹ * (n₁ * l)) * c⁻¹), N.mul_mem (N.inv_mem hn₁)
      ((mem_normalizer_iff.mp (hLN (hCMBL hc)) _).mp hcn), c, hc, by group⟩
  set V := CFSG.inSubgroup CFSG.perfectResidual CMB with hVdef
  have hVC : V ≤ CMB := map_subtype_le _
  have hN₁ : (N.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  set ψ : CMB →* L ⧸ N.subgroupOf L :=
    (QuotientGroup.mk' (N.subgroupOf L)).comp (Subgroup.inclusion hCMBL) with hψ
  have hψs : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf L) q
    obtain ⟨n, hn, c, hc, rfl⟩ := hLNC l hl
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    show ((Subgroup.inclusion hCMBL ⟨c, hc⟩)⁻¹ * ⟨n * c, _⟩ : L).1 ∈ N
    simp only [coe_mul, coe_inv, coe_inclusion]
    have e : (c : G)⁻¹ * (n * c) = c⁻¹ * n * c := by group
    rw [e]
    have := (mem_normalizer_iff.mp (hLN (L.inv_mem (hCMBL hc))) n).mp hn
    simpa using this
  have hQperf : CFSG.perfectResidual (L ⧸ N.subgroupOf L) = ⊤ := by
    have hLtop : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ := by
      apply map_injective L.subtype_injective
      rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hL]
    have hQtop : ⁅(⊤ : Subgroup (L ⧸ N.subgroupOf L)), (⊤ : Subgroup (L ⧸ N.subgroupOf L))⁆ =
        ⊤ := by
      rw [← map_top_of_surjective _ (QuotientGroup.mk'_surjective (N.subgroupOf L)),
        ← map_commutator, hLtop]
    exact le_antisymm le_top
      (CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual ⊤
        (Subgroup.isPerfect_iff.mpr hQtop))
  have hmapV : (CFSG.perfectResidual CMB).map ψ = ⊤ := by
    rw [← hQperf]
    exact CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq ψ hψs
  have hLNV : ∀ l ∈ L, ∃ n ∈ N, ∃ v ∈ V, n * v = l := by
    intro l hl
    obtain ⟨v, hv, hvl⟩ : QuotientGroup.mk' (N.subgroupOf L) ⟨l, hl⟩ ∈
        (CFSG.perfectResidual CMB).map ψ := hmapV ▸ mem_top _
    have h1 : (((v : CMB) : G))⁻¹ * l ∈ N := by
      have := QuotientGroup.eq.mp hvl
      exact this
    refine ⟨(v : G) * ((v : G)⁻¹ * l) * (v : G)⁻¹,
      (mem_normalizer_iff.mp (hLN (hCMBL v.2)) _).mp h1, v, ⟨v, hv, rfl⟩, by group⟩
  have hVperf : ⁅V, V⁆ = V := by
    have h := Subgroup.isPerfect_iff.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect (G := CMB))
    rw [hVdef, CFSG.inSubgroup, ← map_commutator]
    exact congrArg (Subgroup.map CMB.subtype) h
  have hVB : V ≤ centralizer (B : Set G) := hVC.trans inf_le_right
  have hVP : V ≤ normalizer (P : Set G) := hVC.trans (inf_le_left.trans inf_le_right)
  have hVR : V ≤ normalizer (R : Set G) := by
    intro v hv
    rw [mem_normalizer_iff_map_conj_eq, ← hPB, map_commutator,
      (mem_normalizer_iff_map_conj_eq).mp (hVP hv),
      (mem_normalizer_iff_map_conj_eq).mp (centralizer_le_normalizer _ (hVB hv))]
  have hVRT : ⁅V, R⁆ ≤ T := by
    refine le_inf ((le_normalizer_iff_commutator_le_right.mp hVR).trans hRP) ?_
    rw [commutator_comm]
    exact (commutator_mono le_rfl (hVC.trans hCMBL)).trans hRLθ
  have hRV : ⁅R, V⁆ = ⊥ := by
    rw [← hRB]
    refine commutator_commutator_eq_bot_of_rotate ?_ ?_
    · have : ⁅B, V⁆ = ⊥ := by
        rw [commutator_comm]
        exact commutator_eq_bot_iff_le_centralizer.mpr hVB
      rw [this, commutator_bot_left]
    · exact le_bot_iff.mp ((commutator_mono hVRT le_rfl).trans
        (commutator_eq_bot_iff_le_centralizer.mpr hTB).le)
  have hVcR : V ≤ centralizer (R : Set G) := by
    rw [commutator_comm] at hRV
    exact commutator_eq_bot_iff_le_centralizer.mp hRV
  set CL := L ⊓ centralizer ((R ⊔ B : Subgroup G) : Set G) with hCLdef
  have hcentRB : centralizer ((R ⊔ B : Subgroup G) : Set G) =
      centralizer (R : Set G) ⊓ centralizer (B : Set G) := by
    rw [sup_eq_closure, centralizer_closure]
    ext x
    simp only [mem_inf, mem_centralizer_iff, Set.mem_union, SetLike.mem_coe]
    constructor
    · intro h
      exact ⟨fun y hy => h y (Or.inl hy), fun y hy => h y (Or.inr hy)⟩
    · rintro ⟨h1, h2⟩ y (hy | hy)
      · exact h1 y hy
      · exact h2 y hy
  have hVCL : V ≤ CL := le_inf (hVC.trans hCMBL) (hcentRB ▸ le_inf hVcR hVB)
  have hVK : V ≤ K := by
    have hperfV : Group.IsPerfect (V.subgroupOf CL) := by
      rw [Subgroup.isPerfect_iff]
      apply map_injective CL.subtype_injective
      rw [map_commutator, map_subgroupOf_eq_of_le hVCL, hVperf]
    have hle := CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual _ hperfV
    intro v hv
    exact ⟨⟨v, hVCL hv⟩, hle hv, rfl⟩
  have hKCL : K ≤ CL := map_subtype_le _
  have hKcent : K ≤ centralizer (R : Set G) ⊓ centralizer (B : Set G) :=
    hcentRB ▸ hKCL.trans inf_le_right
  refine ⟨?_, hKcent.trans inf_le_left, hKcent.trans inf_le_right, ?_⟩
  · have h := Subgroup.isPerfect_iff.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect (G := CL))
    show ⁅CFSG.inSubgroup CFSG.perfectResidual CL, CFSG.inSubgroup CFSG.perfectResidual CL⁆ =
      CFSG.inSubgroup CFSG.perfectResidual CL
    rw [CFSG.inSubgroup, ← map_commutator]
    exact congrArg (Subgroup.map CL.subtype) h
  · ext l
    constructor
    · intro hl
      obtain ⟨n, hn, v, hv, rfl⟩ := hLNV l hl
      exact ⟨n, hn, v, hVK hv, rfl⟩
    · rintro ⟨n, hn, k, hk, rfl⟩
      exact L.mul_mem (hNL hn) (hKCL hk).1

end CFSG.RankThree.GroupTheory.SteinbergBM
