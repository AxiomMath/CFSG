module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu
public import CFSG.Quasithin.Vol2.KGFactJ4L5NSD
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213C2
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4D
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4E

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Quasithin.A4
open scoped commutatorElement

namespace NoJ4

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem coe_mem_pCoreOf_iff {X : Subgroup G} (x : ↥X) :
    (x : G) ∈ pCoreOf 2 X ↔ x ∈ CFSG.pCore 2 ↥X := CFSG.mem_openPCoreOf_iff x

theorem mem_normalizer_commutator_of {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have h : ⁅A, B⁆ ≤ (⁅A, B⁆).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj g).toMonoidHom ⁅a, b⁆ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hA a).mp ha)
      ((Subgroup.mem_normalizer_iff.mp hB b).mp hb)
  exact Subgroup.mem_normalizer_fintype fun z hz => by simpa using h hz

theorem pCoreOf_LH_le_pCoreOf (hBlk : J4BlockFacts) {T M L I H K : Subgroup G}
    (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) : pCoreOf 2 (perfectCore (L ⊓ H)) ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← v_eq hBlk c h6]
  have hRLT : reducedAggregate (L ⊔ T) ≤ L ⊔ T := by
    rw [← c.omega_eq]
    exact (omegaOneCenterOf_le _).trans (pCoreOf_le 2 _)
  have hVL : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ L :=
    commutator_le_right_of_le_normalizer (hRLT.trans
      (_root_.sup_le Subgroup.le_normalizer (c.hyp421.T_le.trans c.normal)))
  have hVO : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ L ⊓ pCoreOf 2 (L ⊔ T) :=
    le_inf hVL (c.V_le_omega.trans (omegaOneCenterOf_le _))
  refine hVO.trans (le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((pCoreOf_isPGroup 2 (L ⊔ T)).to_le inf_le_right))
  intro y hy
  exact mem_normalizer_inf (Subgroup.le_normalizer hy)
    (le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_left hy))

theorem exists_modO2_equiv_compat (hBlk : J4BlockFacts) {T M L I H K : Subgroup G}
    (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) (hLHL : perfectCore (L ⊓ H) ≤ L) :
    ∃ ι : ModO2 (perfectCore (L ⊓ H)) ≃* ModO2 L, ∀ x : ↥(perfectCore (L ⊓ H)),
      ι (x : ModO2 (perfectCore (L ⊓ H))) = (Subgroup.inclusion hLHL x : ModO2 L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LH := perfectCore (L ⊓ H) with hLH
  have hLHn : LH ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hLHL.trans (le_normalizer_pCoreOf 2 L)
  have hEL : pCoreOf 2 LH ≤ pCoreOf 2 L := pCoreOf_LH_le_pCoreOf hBlk c h6
  set f : ↥LH →* ModO2 L := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
    (Subgroup.inclusion hLHL) with hf
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, o, ho, hao⟩ := (mem_sup_of_le_normalizer hLHn).mp (c.L_le y.2)
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hoL : o ∈ L := pCoreOf_le 2 L ho
    have e : (Subgroup.inclusion hLHL ⟨a, ha⟩)⁻¹ * y = ⟨o, hoL⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hao]
      group
    rw [e]
    exact (coe_mem_pCoreOf_iff (X := L) ⟨o, hoL⟩).mp ho
  have hker : f.ker = CFSG.pCore 2 ↥LH := by
    ext x
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, ← coe_mem_pCoreOf_iff, ← coe_mem_pCoreOf_iff,
      Subgroup.coe_inclusion]
    exact ⟨fun h => inf_pCoreOf_le L H ⟨x.2, h⟩, fun h => hEL h⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfs), fun x => rfl⟩

theorem modO2_equiv (hBlk : J4BlockFacts) {T M L I H K : Subgroup G}
    (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) : Nonempty (ModO2 (perfectCore (L ⊓ H)) ≃* ModO2 L) := by
  obtain ⟨ι, -⟩ := exists_modO2_equiv_compat hBlk c h6
    ((perfectCore_le (L ⊓ H)).trans inf_le_left)
  exact ⟨ι⟩

theorem isExt_LH_of_l5 {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
    (h5 : C31Case6L5 (H ⊓ M) (perfectCore (L ⊓ H))) :
    IsExt ↥(perfectCore (L ⊓ H)) (fun N _ => IsE2 10 N) (fun Y _ => IsPSL 5 2 1 Y) := by
  set LH := perfectCore (L ⊓ H) with hLH
  have hM0 : conjClosure LH (H ⊓ M) = LH := by
    refine le_antisymm (conjClosure_le fun h hh z hz => ?_) (le_conjClosure LH (H ⊓ M))
    exact (Subgroup.mem_normalizer_iff.mp (c.LH_normal hh) z).mp hz
  have h' : IsExt ↥(conjClosure LH (H ⊓ M)) (fun N _ => IsE2 10 N)
    (fun Y _ => IsPSL 5 2 1 Y) := h5
  rwa [hM0] at h'

theorem centralizerSection_le {L T : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hZ : Subgroup.center (ModO2 L) = ⊥) :
    centralizerSection (L ⊔ T) L (pCoreOf 2 L) ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizerSection (L ⊔ T) L (pCoreOf 2 L) with hC
  have hLTL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := _root_.sup_le Subgroup.le_normalizer hTL
  have hCL : ∀ c ∈ C, c ∈ L → c ∈ pCoreOf 2 L := by
    intro c hc hcL
    have hmem : (QuotientGroup.mk (⟨c, hcL⟩ : ↥L) : ModO2 L) ∈ Subgroup.center (ModO2 L) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        ← coe_mem_pCoreOf_iff]
      have h1 := hc.2.2.2 (y⁻¹ : ↥L) (y⁻¹ : ↥L).2
      have e : (((y * ⟨c, hcL⟩)⁻¹ * (⟨c, hcL⟩ * y) : ↥L) : G) =
          c⁻¹ * (((y⁻¹ : ↥L) : G) * c * ((y⁻¹ : ↥L) : G)⁻¹ * c⁻¹) * c := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L (L.inv_mem hcL)) _).mp
        h1
      simpa using this
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact (coe_mem_pCoreOf_iff (X := L) ⟨c, hcL⟩).mpr hmem
  have hC2 : IsPGroup 2 ↥C := by
    rintro ⟨c, hc⟩
    have hcLT : c ∈ L ⊔ T := hc.1
    rw [sup_comm] at hcLT
    obtain ⟨t, ht, l, hl, rfl⟩ := (mem_sup_of_le_normalizer hTL).mp hcLT
    have key : ∀ n : ℕ, ∃ l' ∈ L, (t * l) ^ n = t ^ n * l' := by
      intro n
      induction n with
      | zero => exact ⟨1, L.one_mem, by simp⟩
      | succ n ih =>
        obtain ⟨l', hl', he⟩ := ih
        refine ⟨t⁻¹ * l' * t * l, L.mul_mem ?_ hl, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTL ht)) l').mp hl'
          simpa using this
        · rw [pow_succ, he, pow_succ]
          group
    obtain ⟨a, ha⟩ := hT ⟨t, ht⟩
    have ha' : t ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    obtain ⟨l', hl', he⟩ := key (2 ^ a)
    have hpowL : (t * l) ^ 2 ^ a ∈ L := by rw [he, ha', one_mul]; exact hl'
    have hpowO := hCL _ (C.pow_mem hc _) hpowL
    obtain ⟨b, hb⟩ := (pCoreOf_isPGroup 2 L) ⟨_, hpowO⟩
    have hb' : ((t * l) ^ 2 ^ a) ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    refine ⟨a + b, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, hb']
  have hCN : L ⊔ T ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun c hc => ?_
    have hgL := hLTL hg
    have hgO := normalizer_le_normalizer_pCoreOf 2 L hgL
    refine ⟨(L ⊔ T).mul_mem ((L ⊔ T).mul_mem hg hc.1) ((L ⊔ T).inv_mem hg),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgL hc.2.1) (Subgroup.inv_mem _ hgL),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgO hc.2.2.1) (Subgroup.inv_mem _ hgO),
      fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgL) x).mp hx
      simpa using this
    have h1 := hc.2.2.2 _ hx'
    have e : x * (g * c * g⁻¹) * x⁻¹ * (g * c * g⁻¹)⁻¹ =
        g * ((g⁻¹ * x * g) * c * (g⁻¹ * x * g)⁻¹ * c⁻¹) * g⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hgO _).mp h1
  exact le_pCoreOf_of_le_normalizer 2 (fun c hc => hc.1) hCN hC2

theorem le_sup_pCoreOf_of_inner {L T : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hZ : Subgroup.center (ModO2 L) = ⊥)
    (hin : ∀ t ∈ T, ∃ l ∈ L, ∀ y ∈ L, t * l * y * (t * l)⁻¹ * y⁻¹ ∈ pCoreOf 2 L) :
    T ≤ L ⊔ pCoreOf 2 (L ⊔ T) := by
  intro t ht
  obtain ⟨l, hl, hy⟩ := hin t ht
  have htlL : t * l ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (hTL ht) (Subgroup.le_normalizer hl)
  have hC : t * l ∈ centralizerSection (L ⊔ T) L (pCoreOf 2 L) := by
    refine ⟨(L ⊔ T).mul_mem (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left hl), htlL,
      normalizer_le_normalizer_pCoreOf 2 L htlL, fun x hx => ?_⟩
    have h1 := hy x⁻¹ (L.inv_mem hx)
    have e : x * (t * l) * x⁻¹ * (t * l)⁻¹ = x * (t * l * x⁻¹ * (t * l)⁻¹ * x⁻¹⁻¹) * x⁻¹ := by
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L hx) _).mp h1
  have h2 := centralizerSection_le hT hTL hZ hC
  have e : t = (t * l) * l⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left (L.inv_mem hl))

omit [Finite G] in
theorem exists_inner_of_m24
    {L : Subgroup G}
    (hM : IsSporadic .M24 (ModO2 L)) {t : G} (ht : t ∈ Subgroup.normalizer (L : Set G)) :
    ∃ l ∈ L, ∀ y ∈ L, t * l * y * (t * l)⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
  classical
  have hmem : ∀ y ∈ L, t * y * t⁻¹ ∈ L := fun y hy => (Subgroup.mem_normalizer_iff.mp ht y).mp hy
  have hmem' : ∀ y ∈ L, t⁻¹ * y * t ∈ L := fun y hy => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) y).mp hy
    simpa using this
  let σ : ↥L ≃* ↥L :=
    { toFun := fun y => ⟨t * y * t⁻¹, hmem y y.2⟩
      invFun := fun y => ⟨t⁻¹ * y * t, hmem' y y.2⟩
      left_inv := fun y => Subtype.ext (show t⁻¹ * (t * (y : G) * t⁻¹) * t = y by group)
      right_inv := fun y => Subtype.ext (show t * (t⁻¹ * (y : G) * t) * t⁻¹ = y by group)
      map_mul' := fun a b => Subtype.ext (show t * ((a : G) * b) * t⁻¹ =
          (t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹) by group) }
  let φ : ModO2 L ≃* ModO2 L :=
    QuotientGroup.congr (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥L) σ (CFSG.pCore_map_iso 2 σ)
  obtain ⟨e₀⟩ := hM
  let e : ModO2 L ≃* CFSG.Blueprint.NativeSporadic.M24 := e₀
  obtain ⟨h, hh⟩ := QuasithinUnique.Ch1.m24_all_inner ((e.symm.trans φ).trans e)
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective (e.symm h)
  have hφ : ∀ z : ModO2 L, φ z = e.symm h * z * (e.symm h)⁻¹ := by
    intro z
    have h1 := congrArg (fun α : MulAut CFSG.Blueprint.NativeSporadic.M24 => α (e z)) hh
    simp only [MulAut.conj_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    apply e.injective
    rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  refine ⟨((y₀⁻¹ : ↥L) : G), (y₀⁻¹ : ↥L).2, fun y hy => ?_⟩
  set y' : ↥L := y₀⁻¹ * ⟨y, hy⟩ * y₀ with hy'
  have h2 := hφ (QuotientGroup.mk y')
  rw [← hy₀, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h2
  have h3 : φ (QuotientGroup.mk y') = QuotientGroup.mk (σ y') := QuotientGroup.congr_mk _ _ _ _ _
  rw [h3, QuotientGroup.eq, ← coe_mem_pCoreOf_iff] at h2
  have e4 : (((σ y')⁻¹ * (y₀ * y' * y₀⁻¹) : ↥L) : G) =
      (t * ((y₀⁻¹ : ↥L) : G) * y * ((y₀⁻¹ : ↥L) : G)⁻¹ * t⁻¹)⁻¹ * y := by
    simp only [hy', Subgroup.coe_mul, Subgroup.coe_inv, σ, MulEquiv.coe_mk, Equiv.coe_fn_mk]
    group
  rw [e4] at h2
  have e5 : t * ((y₀⁻¹ : ↥L) : G) * y * (t * ((y₀⁻¹ : ↥L) : G))⁻¹ * y⁻¹ =
      y * ((t * ((y₀⁻¹ : ↥L) : G) * y * ((y₀⁻¹ : ↥L) : G)⁻¹ * t⁻¹)⁻¹ * y)⁻¹ * y⁻¹ := by group
  rw [e5]
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L hy) _).mp
    ((pCoreOf 2 L).inv_mem h2)

theorem isE2_of_l5 {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
    (hL52 : IsPSL 5 2 1 (ModO2 (perfectCore (L ⊓ H))))
    (h5 : C31Case6L5 (H ⊓ M) (perfectCore (L ⊓ H))) :
    IsE2 10 ↥(pCoreOf 2 (perfectCore (L ⊓ H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LH := perfectCore (L ⊓ H) with hLH
  have h5' : IsExt ↥LH (fun N _ => IsE2 10 N) (fun Y _ => IsPSL 5 2 1 Y) := by
    have h : IsExt ↥(conjClosure LH (H ⊓ M)) (fun N _ => IsE2 10 N)
        (fun Y _ => IsPSL 5 2 1 Y) := h5
    rwa [conjClosure_LH c] at h
  obtain ⟨N, hN, hNE, hNQ⟩ := h5'
  have hcardN : Nat.card ↥N = 2 ^ 10 := by
    obtain ⟨e⟩ := hNE
    rw [Nat.card_congr e.toEquiv]
    simp
  have hN2 : IsPGroup 2 ↥N := IsPGroup.of_card hcardN
  have hNle : N ≤ CFSG.pCore 2 ↥LH := le_sSup ⟨hN, hN2⟩
  have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥LH)
  have hc1 : Nat.card (↥LH ⧸ N) = 9999360 := F420.card_of_l52 hNQ
  have hc2 : Nat.card (↥LH ⧸ CFSG.pCore 2 ↥LH) = 9999360 := F420.card_of_l52 hL52
  rw [hc1] at e1
  rw [hc2] at e2
  have hNP : N = CFSG.pCore 2 ↥LH :=
    Subgroup.eq_of_le_of_card_ge hNle (by omega)
  have eN : ↥N ≃* ↥(pCoreOf 2 LH) :=
    (MulEquiv.subgroupCongr hNP).trans (((CFSG.pCore 2 ↥LH).equivMapOfInjective LH.subtype
      LH.subtype_injective).trans
        (MulEquiv.subgroupCongr (C2A3Orbits.pCoreOf_eq_map_pCore LH).symm))
  exact isE2_of_mulEquiv 10 _ _ eN hNE

theorem le_sup_pCoreOf
    (hBlk : J4BlockFacts)
    (hNC : J4L5BlockNotSelfDual) {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) : T ≤ L ⊔ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LH := perfectCore (L ⊓ H) with hLH
  set E := pCoreOf 2 LH with hE
  have hT : IsPGroup 2 ↥T := c.hyp421.sylow.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := c.hyp421.T_le.trans c.normal
  obtain ⟨e⟩ := modO2_equiv hBlk c h6
  have hZ : Subgroup.center (ModO2 L) = ⊥ := by
    have h1 := center_map_mulEquiv e
    rw [modO2_center_eq_bot h6, Subgroup.map_bot] at h1
    exact h1.symm
  refine le_sup_pCoreOf_of_inner hT hTL hZ fun t ht => ?_
  rcases h6.2.2 with ⟨hM24, -⟩ | ⟨hL52, h5⟩
  · exact exists_inner_of_m24 (isSporadic_of_mulEquiv .M24 _ _ e hM24) (hTL ht)
  · have hVE : ⁅reducedAggregate (L ⊔ T), L⁆ = E := v_eq hBlk c h6
    have hEL : E ≤ pCoreOf 2 L := pCoreOf_LH_le_pCoreOf hBlk c h6
    have hfacts := blockFacts_of_case6 hBlk c h6
    have hKC : K ⊓ Subgroup.centralizer (E : Set G) = E := hfacts.2.1
    have hLHL : LH ≤ L := (perfectCore_le (L ⊓ H)).trans inf_le_left
    have hLE : L ≤ Subgroup.normalizer (E : Set G) := by
      rw [← hVE]
      exact Subgroup.normalizer_commutator_ge_right _ L
    have hOC : pCoreOf 2 L ≤ Subgroup.centralizer (E : Set G) := by
      rw [← hVE]
      exact c.pCoreOf_le_centralizer_V c.pCoreOf_L_le
    have hRN : L ⊔ T ≤ Subgroup.normalizer (reducedAggregate (L ⊔ T) : Set G) := by
      rw [← c.omega_eq]
      exact (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_omegaOneCenterOf _)
    obtain ⟨ι, hι⟩ := exists_modO2_equiv_compat hBlk c h6 hLHL
    have hNCL : SingerNoConj G L E := singerNoConj_of_quot hLHL hOC ι hι
      (hNC G K LH h6.1 c.LH_le h6.2.1 (isExt_LH_of_l5 c h5))
    refine j4L5BlockInner_of_noConj (isPSL_of_mulEquiv 5 2 1 _ _ e hL52) (isE2_of_l5 c hL52 h5)
      hLE ?_ hNCL (hTL ht) ?_
    ·
      refine le_antisymm (fun y hy => ?_) (le_inf (pCoreOf_le 2 L) hOC)
      obtain ⟨a, ha, o, ho, rfl⟩ :=
        (mem_sup_of_le_normalizer (hLHL.trans (le_normalizer_pCoreOf 2 L))).mp (c.L_le hy.1)
      have haC : a ∈ Subgroup.centralizer (E : Set G) := by
        have := (Subgroup.centralizer (E : Set G)).mul_mem hy.2
          ((Subgroup.centralizer (E : Set G)).inv_mem (hOC ho))
        simpa using this
      have haE : a ∈ E := by
        rw [← hKC]
        exact ⟨c.LH_le ha, haC⟩
      exact (pCoreOf 2 L).mul_mem (hEL haE) ho
    ·
      change t ∈ Subgroup.normalizer (E : Set G)
      rw [← hVE]
      exact mem_normalizer_commutator_of (hRN (Subgroup.mem_sup_right ht)) (hTL ht)

end NoJ4

end CFSG.Quasithin.H13.Ch4
