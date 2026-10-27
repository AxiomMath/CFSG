module

public import CFSG.LocalAnalysis.StandardType.GGSporKStepThree
public import CFSG.LocalAnalysis.StandardType.GGSporKStepZero
public import CFSG.LocalAnalysis.StandardType.GGSporKLayer

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

private theorem gk4_Exists_orderOf_eq_p_centralizes {W : Type} [Group W] {p : ℕ} (hp : p.Prime)
    {N : Subgroup W} [Finite N] (hpN : p ∣ Nat.card N) {z : W} (hz : orderOf z = p)
    (hzN : z ∈ Subgroup.normalizer (N : Set W)) :
    ∃ u ∈ N, orderOf u = p ∧ z * u = u * z := by
  have : Fact p.Prime := ⟨hp⟩
  let g : Subgroup.normalizer (N : Set W) := ⟨z, hzN⟩
  let T : Subgroup (Subgroup.normalizer (N : Set W)) := Subgroup.zpowers g
  have hg : orderOf g = p := by
    rw [← hz]
    exact (Subgroup.orderOf_coe g).symm
  have hT : IsPGroup p T := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hmod := hT.card_modEq_card_fixedPoints N
  have hdvd : p ∣ Nat.card (MulAction.fixedPoints T N) :=
    (hmod.dvd_iff (dvd_refl p)).mp hpN
  let S : Subgroup N := (Subgroup.centralizer ({z} : Set W)).subgroupOf N
  have hset : (MulAction.fixedPoints T N : Set N) = (S : Set N) := by
    ext a
    simp only [SetLike.mem_coe]
    constructor
    · intro ha
      have h1 : g • a = a := ha ⟨g, Subgroup.mem_zpowers g⟩
      have h2 : z * (a : W) * z⁻¹ = a := congrArg Subtype.val h1
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      calc (a : W) * z = z * (a : W) * z⁻¹ * z := by rw [h2]
        _ = z * (a : W) := by group
    · intro ha t
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at ha
      have h1 : g • a = a := by
        apply Subtype.ext
        change z * (a : W) * z⁻¹ = a
        calc z * (a : W) * z⁻¹ = (a : W) * z * z⁻¹ := by rw [ha]
          _ = a := by group
      have h2 : g ∈ MulAction.stabilizer (Subgroup.normalizer (N : Set W)) a := h1
      obtain ⟨t, ht⟩ := t
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
      exact (MulAction.stabilizer _ a).zpow_mem h2 m
  have hcard : Nat.card (MulAction.fixedPoints T N) = Nat.card S := by
    rw [hset]
    rfl
  rw [hcard] at hdvd
  have : Finite S := Finite.of_injective _ S.subtype_injective
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := S) p hdvd
  refine ⟨((u : N) : W), (u : N).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hu]
  · have h := u.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at h
    exact h.symm

private theorem gk4_IsElemAbelian_closure {W : Type} [Group W] {p : ℕ} {S : Set W}
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hpow : ∀ a ∈ S, a ^ p = 1) :
    IsElemAbelian p (Subgroup.closure S) := by
  have hpair : S.Pairwise Commute := fun a ha b hb _ => hcomm a ha b hb
  haveI := Subgroup.isMulCommutative_closure hpair
  have hcomm' : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (mul_comm' ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨Subgroup.isMulCommutative_closure hpair, ?_⟩
  intro x hx
  refine Subgroup.closure_induction (p := fun y _ => y ^ p = 1) ?_ ?_ ?_ ?_ hx
  · intro a ha; exact hpow a ha
  · exact one_pow p
  · intro a b ha hb iha ihb
    have hc : Commute a b := hcomm' a ha b hb
    rw [hc.mul_pow, iha, ihb, one_mul]
  · intro a ha iha
    rw [inv_pow, iha, inv_one]

private theorem gk4_Center_eq_bot_of_isSimpleGroup {X : Type*} [Group X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a) hab

private def gk4_DJ {W : Type} [Group W] (e : W) (K : Subgroup W) : Subgroup W :=
  K ⊓ Subgroup.centralizer ({e} : Set W)

private noncomputable def gk4_OJ (p : ℕ) {W : Type} [Group W] (e : W) (K : Subgroup W) :
    Subgroup W :=
  (CFSG.pCore p ↥(gk4_DJ e K)).map (gk4_DJ e K).subtype

private noncomputable def gk4_ZJ (p : ℕ) {W : Type} [Group W] (e : W) (K : Subgroup W) :
    Subgroup W :=
  (Subgroup.center ↥(gk4_OJ p e K)).map (gk4_OJ p e K).subtype

private noncomputable def gk4_AJ (p : ℕ) {W : Type} [Group W] (e : W) (K : Subgroup W) :
    Subgroup W :=
  Subgroup.closure {z : W | z ∈ gk4_ZJ p e K ∧ z ^ p = 1}

private theorem gk4_AJ_le_DJ (p : ℕ) {W : Type} [Group W] (e : W) (K : Subgroup W) :
    gk4_AJ p e K ≤ gk4_DJ e K :=
  (Subgroup.closure_le _).mpr fun z hz =>
    (Subgroup.map_subtype_le (CFSG.pCore p ↥(gk4_DJ e K)))
      (Subgroup.map_subtype_le (Subgroup.center ↥(gk4_OJ p e K)) hz.1)

private theorem gk4_AJ_le_centralizer (p : ℕ) {W : Type} [Group W] (e : W) (K : Subgroup W) :
    gk4_AJ p e K ≤ Subgroup.centralizer ({e} : Set W) :=
  (gk4_AJ_le_DJ p e K).trans inf_le_right

private theorem gk4_AJ_le_component (p : ℕ) {W : Type} [Group W] (e : W) (K : Subgroup W) :
    gk4_AJ p e K ≤ K :=
  (gk4_AJ_le_DJ p e K).trans inf_le_left

private theorem gk4_AJ_le_ZJ (p : ℕ) {W : Type} [Group W] (e : W) (K : Subgroup W) :
    gk4_AJ p e K ≤ gk4_ZJ p e K :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1

private theorem gk4_ZJ_comm (p : ℕ) {W : Type} [Group W] (e : W) (K : Subgroup W)
    {a b : W} (ha : a ∈ gk4_ZJ p e K) (hb : b ∈ gk4_ZJ p e K) : a * b = b * a := by
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
  have h := Subgroup.mem_center_iff.mp ha' b'
  exact congrArg (fun z : ↥(gk4_OJ p e K) => (z : W)) h.symm

private theorem gk4_AJ_isElemAbelian (p : ℕ) {W : Type} [Group W] (e : W) (K : Subgroup W) :
    IsElemAbelian p (gk4_AJ p e K) :=
  gk4_IsElemAbelian_closure (fun _ ha _ hb => gk4_ZJ_comm p e K ha.1 hb.1)
    (fun _ ha => ha.2)

private theorem gk4_PPrimeCore_subgroup_bot {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hP' : CFSG.pPrimeCore p G = ⊥) {Y : Subgroup G} (hY : Y.IsSubnormal) :
    CFSG.pPrimeCore p ↥Y = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro K hKn hKcop
  have hKsub : (K.map Y.subtype).IsSubnormal :=
    Subgroup.IsSubnormal.trans' hKn.isSubnormal hY
  have hcop : ¬ p ∣ Nat.card ↥(K.map Y.subtype) := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hKcop
  have hle : K.map Y.subtype ≤ CFSG.pPrimeCore p G :=
    ggLe_pPrimeCore_of_isSubnormal (p := p) hKsub hcop
  rw [hP'] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective K Y.subtype_injective).mp (le_bot_iff.mp hle)

private theorem gk4_Layer_subgroup_bot {G : Type} [Group G] [Finite G]
    (hlayer : CFSG.layer G = ⊥) {Y : Subgroup G} (hY : Y.IsSubnormal) :
    CFSG.layer ↥Y = ⊥ := by
  rw [CFSG.layer.eq_sSup, sSup_eq_bot]
  intro K hK
  exfalso
  have hK' : CFSG.IsComponent (K.map Y.subtype) :=
    CFSG.LocalAnalysis.ComponentInitial.component_subnormal_lift hY hK
  have hle : K.map Y.subtype ≤ CFSG.layer G := le_sSup hK'
  rw [hlayer] at hle
  have hKbot : K = ⊥ := (Subgroup.map_eq_bot_iff_of_injective K Y.subtype_injective).mp
    (le_bot_iff.mp hle)
  exact (Subgroup.nontrivial_iff_ne_bot K).mp
    (CFSG.LocalCores.isQuasisimple_nontrivial hK.1) hKbot

private theorem gk4_PCore_ne_bot_of_isSubnormal {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hP' : CFSG.pPrimeCore p G = ⊥) (hlayer : CFSG.layer G = ⊥)
    {Y : Subgroup G} (hY : Y.IsSubnormal) (hYne : Y ≠ ⊥) : CFSG.pCore p ↥Y ≠ ⊥ := by
  intro hbot
  have hP'Y : CFSG.pPrimeCore p ↥Y = ⊥ := gk4_PPrimeCore_subgroup_bot hP' hY
  have hlayerY : CFSG.layer ↥Y = ⊥ := gk4_Layer_subgroup_bot hlayer hY
  have hfit : CFSG.fittingSubgroup ↥Y = CFSG.pCore p ↥Y := CFSG.Fitting_eq_pcore ↥Y p hP'Y
  have hgen : CFSG.generalizedFitting ↥Y = CFSG.pCore p ↥Y := by
    rw [CFSG.generalizedFitting, hlayerY, sup_bot_eq, hfit]
  have hcen := CFSG.centralizer_generalizedFitting_le ↥Y
  rw [hgen, hbot] at hcen
  haveI : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hYne
  obtain ⟨y, hy1⟩ := exists_ne (1 : ↥Y)
  have hycen : y ∈ Subgroup.centralizer ((⊥ : Subgroup ↥Y) : Set ↥Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz1 : z = 1 := Subgroup.mem_bot.mp hz
    rw [hz1, one_mul, mul_one]
  exact hy1 (Subgroup.mem_bot.mp (hcen hycen))

private theorem gk4_Centralizer_map_conj {W : Type} [Group W] (e c : W)
    (hc : c ∈ Subgroup.centralizer ({e} : Set W)) :
    Subgroup.map (MulAut.conj c).toMonoidHom (Subgroup.centralizer ({e} : Set W)) =
      Subgroup.centralizer ({e} : Set W) := by
  have hce : c * e = e * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have hye : e * y = y * e := hy e (Set.mem_singleton e)
    have hce' : e * c⁻¹ = c⁻¹ * e := by
      have h := congrArg (fun z => c⁻¹ * z * c⁻¹) hce
      simpa [mul_assoc] using h
    calc e * (c * y * c⁻¹) = (e * c) * y * c⁻¹ := by group
      _ = (c * e) * y * c⁻¹ := by rw [← hce]
      _ = c * (e * y) * c⁻¹ := by group
      _ = c * (y * e) * c⁻¹ := by rw [hye]
      _ = c * y * (e * c⁻¹) := by group
      _ = c * y * (c⁻¹ * e) := by rw [hce']
      _ = (c * y * c⁻¹) * e := by group
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨c⁻¹ * x * c, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have hxe : e * x = x * e := hx e (Set.mem_singleton e)
      have hce' : e * c⁻¹ = c⁻¹ * e := by
        have h := congrArg (fun z => c⁻¹ * z * c⁻¹) hce
        simpa [mul_assoc] using h
      calc e * (c⁻¹ * x * c) = (e * c⁻¹) * x * c := by group
        _ = (c⁻¹ * e) * x * c := by rw [hce']
        _ = c⁻¹ * (e * x) * c := by group
        _ = c⁻¹ * (x * e) * c := by rw [hxe]
        _ = (c⁻¹ * x * c) * e := by
          rw [show (c⁻¹ * x * c) * e = c⁻¹ * (x * (c * e)) from by group, hce]
          group
    · show c * (c⁻¹ * x * c) * c⁻¹ = x
      group

private theorem gk4_DJ_map {W : Type} [Group W] (e c : W)
    (hc : c ∈ Subgroup.centralizer ({e} : Set W)) (K : Subgroup W) :
    gk4_DJ e (K.map (MulAut.conj c).toMonoidHom) =
      (gk4_DJ e K).map (MulAut.conj c).toMonoidHom := by
  rw [gk4_DJ, gk4_DJ, Subgroup.map_inf K (Subgroup.centralizer ({e} : Set W))
    (MulAut.conj c).toMonoidHom (MulAut.conj c).injective, gk4_Centralizer_map_conj e c hc]

private theorem gk4_OJ_map (p : ℕ) {W : Type} [Group W] (e c : W)
    (hc : c ∈ Subgroup.centralizer ({e} : Set W)) (K : Subgroup W) :
    Subgroup.map (MulAut.conj c).toMonoidHom (gk4_OJ p e K) =
      gk4_OJ p e (K.map (MulAut.conj c).toMonoidHom) := by
  let φ := MulAut.conj c
  let D : Subgroup W := gk4_DJ e K
  have hD : gk4_DJ e (K.map φ.toMonoidHom) = D.map φ.toMonoidHom := gk4_DJ_map e c hc K
  let eD : ↥D ≃* ↥(D.map φ.toMonoidHom) := D.equivMapOfInjective φ.toMonoidHom φ.injective
  have hcomp : φ.toMonoidHom.comp D.subtype =
      (D.map φ.toMonoidHom).subtype.comp eD.toMonoidHom := by
    ext x
    exact (Subgroup.coe_equivMapOfInjective_apply D φ.toMonoidHom φ.injective x).symm
  calc Subgroup.map φ.toMonoidHom (gk4_OJ p e K)
      = (CFSG.pCore p ↥D).map (φ.toMonoidHom.comp D.subtype) := by
          rw [gk4_OJ, Subgroup.map_map]
    _ = (CFSG.pCore p ↥D).map ((D.map φ.toMonoidHom).subtype.comp eD.toMonoidHom) := by
          rw [hcomp]
    _ = ((CFSG.pCore p ↥D).map eD.toMonoidHom).map (D.map φ.toMonoidHom).subtype := by
          rw [Subgroup.map_map]
    _ = (CFSG.pCore p ↥(D.map φ.toMonoidHom)).map (D.map φ.toMonoidHom).subtype := by
          rw [CFSG.pCore_map_iso p eD]
    _ = gk4_OJ p e (K.map φ.toMonoidHom) := by
          rw [gk4_OJ, hD]

private theorem gk4_ZJ_map (p : ℕ) {W : Type} [Group W] (e c : W)
    (hc : c ∈ Subgroup.centralizer ({e} : Set W)) (K : Subgroup W) :
    Subgroup.map (MulAut.conj c).toMonoidHom (gk4_ZJ p e K) =
      gk4_ZJ p e (K.map (MulAut.conj c).toMonoidHom) := by
  let φ := MulAut.conj c
  let O : Subgroup W := gk4_OJ p e K
  have hO : gk4_OJ p e (K.map φ.toMonoidHom) = O.map φ.toMonoidHom :=
    (gk4_OJ_map p e c hc K).symm
  let eO : ↥O ≃* ↥(O.map φ.toMonoidHom) := O.equivMapOfInjective φ.toMonoidHom φ.injective
  have hcomp : φ.toMonoidHom.comp O.subtype =
      (O.map φ.toMonoidHom).subtype.comp eO.toMonoidHom := by
    ext x
    exact (Subgroup.coe_equivMapOfInjective_apply O φ.toMonoidHom φ.injective x).symm
  calc Subgroup.map φ.toMonoidHom (gk4_ZJ p e K)
      = (Subgroup.center ↥O).map (φ.toMonoidHom.comp O.subtype) := by
          rw [gk4_ZJ, Subgroup.map_map]
    _ = (Subgroup.center ↥O).map ((O.map φ.toMonoidHom).subtype.comp eO.toMonoidHom) := by
          rw [hcomp]
    _ = ((Subgroup.center ↥O).map eO.toMonoidHom).map (O.map φ.toMonoidHom).subtype := by
          rw [Subgroup.map_map]
    _ = (Subgroup.center ↥(O.map φ.toMonoidHom)).map (O.map φ.toMonoidHom).subtype := by
          have hcen : (Subgroup.center ↥O).map eO.toMonoidHom =
              Subgroup.center ↥(O.map φ.toMonoidHom) := Subgroup.map_center_eq eO
          rw [hcen]
    _ = gk4_ZJ p e (K.map φ.toMonoidHom) := by
          rw [gk4_ZJ, hO]

private theorem gk4_AJ_map_le (p : ℕ) {W : Type} [Group W] (e c : W)
    (hc : c ∈ Subgroup.centralizer ({e} : Set W)) (K : Subgroup W) :
    Subgroup.map (MulAut.conj c).toMonoidHom (gk4_AJ p e K) ≤
      gk4_AJ p e (K.map (MulAut.conj c).toMonoidHom) := by
  rw [gk4_AJ, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro x ⟨y, ⟨hyZ, hyp⟩, rfl⟩
  refine ⟨(gk4_ZJ_map p e c hc K).le (Subgroup.mem_map.mpr ⟨y, hyZ, rfl⟩), ?_⟩
  rw [← map_pow, hyp, map_one]

private theorem gk4_IsComponentOf_map_conj {W : Type} [Group W] {H K : Subgroup W}
    (hK : IsComponentOf K H) {c : W} (hc : c ∈ H) :
    IsComponentOf (K.map (MulAut.conj c).toMonoidHom) H := by
  have hHmap : H.map (MulAut.conj c).toMonoidHom = H := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact H.mul_mem (H.mul_mem hc hx) (H.inv_mem hc)
    · intro y hy
      refine ⟨c⁻¹ * y * c, H.mul_mem (H.mul_mem (H.inv_mem hc) hy) hc, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem hc (hK.1 hx)) (H.inv_mem hc)
  · have := hK.2.1.map (MulAut.conj c).toMonoidHom
    rwa [hHmap] at this
  · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (K.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).symm hK.2.2

theorem ggSporK_p_dvd_card_component {W : Type} [Group W] [Finite W] {p : ℕ}
    (hCen : BMNoLiePComp p W) (hG1 : BMPPrimeCore p W) {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat p H E) (hP' : LargeEvenPPrimeCore p ↥H = ⊥)
    (hP : CFSG.pCore p ↥H = ⊥) {J : Subgroup W} (hJ : IsComponentOf J H) :
    p ∣ Nat.card ↥J := by
  by_contra hpJ
  haveI : Fact p.Prime := ⟨hyp.1.1⟩
  have h2 : CFSG.pCore 2 ↥H = ⊥ := ggSporK_pCore_two_eq_bot hyp.1.1 hyp.1.2.1 hP'
  have hEJ : ∀ e ∈ E, ∀ x ∈ J, e * x * e⁻¹ ∈ J := (ggSporK_component_data hyp h2 hJ).1
  have hEnorm : E ≤ Subgroup.normalizer (J : Set W) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    constructor
    · intro hx
      simpa using hEJ e⁻¹ (E.inv_mem he) x hx
    · intro hx
      have h := hEJ e he (e⁻¹ * x * e) hx
      have heq : e * (e⁻¹ * x * e) * e⁻¹ = x := by group
      rwa [heq] at h
  letI : MulDistribMulAction E J :=
    MulDistribMulAction.compHom J (J.normalizerMonoidHom.comp (Subgroup.inclusion hEnorm))
  have hact : ∀ (a : E) (x : J), ((a • x : J) : W) = (a : W) * (x : W) * (a : W)⁻¹ :=
    fun _ _ => rfl
  have hE2 : p ^ 2 ≤ Nat.card E := by rw [hyp.1.2.2.2.1]
  haveI : IsElementaryAbelian p E :=
    { toIsMulCommutative := hyp.1.2.2.1.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
        apply Subtype.ext
        simpa using hyp.1.2.2.1.2 (x : W) x.2 }
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := E) (H := J) hE2 hpJ
  have hfix : ∀ (a : E) (_ : a ≠ 1), fixedPointSubgroup (Subgroup.zpowers a) J = ⊥ := by
    intro a ha1
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have haW : (a : W) ∈ E := a.2
    have haW1 : (a : W) ≠ 1 := fun h => ha1 (Subtype.ext h)
    obtain ⟨hCH, -, hP'C, -⟩ := ggSporK_step_one hCen hG1 hyp haW haW1
    have hax : (a : W) * (x : W) * (a : W)⁻¹ = (x : W) := by
      have := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a x).1 hx
      simpa [hact a x] using congrArg (fun z : J => (z : W)) this
    have hxD : (x : W) ∈ J ⊓ Subgroup.centralizer ({(a : W)} : Set W) :=
      ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp hax).symm⟩
    set D : Subgroup W := J ⊓ Subgroup.centralizer ({(a : W)} : Set W) with hD
    have hDsub : CFSG.Assembly.IsSubnormal D (Subgroup.centralizer ({(a : W)} : Set W)) :=
      hJ.2.1.inf_of_le hCH
    have hDcop : ¬ p ∣ Nat.card ↥D := fun hd =>
      hpJ (hd.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hNsn : (D.subgroupOf (Subgroup.centralizer ({(a : W)} : Set W))).IsSubnormal :=
      hDsub.subgroupOf
    have hNcop : ¬ p ∣ Nat.card ↥(D.subgroupOf (Subgroup.centralizer ({(a : W)} : Set W))) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
      exact hDcop
    have hN : (D.subgroupOf (Subgroup.centralizer ({(a : W)} : Set W))) ≤
        CFSG.pPrimeCore p ↥(Subgroup.centralizer ({(a : W)} : Set W)) :=
      ggLe_pPrimeCore_of_isSubnormal hNsn hNcop
    have hP'C' : CFSG.pPrimeCore p ↥(Subgroup.centralizer ({(a : W)} : Set W)) = ⊥ := hP'C
    have hDbot : D = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hyN : (⟨y, hy.2⟩ : ↥(Subgroup.centralizer ({(a : W)} : Set W))) ∈
          D.subgroupOf (Subgroup.centralizer ({(a : W)} : Set W)) :=
        Subgroup.mem_subgroupOf.mpr hy
      have hmem : (⟨y, hy.2⟩ : ↥(Subgroup.centralizer ({(a : W)} : Set W))) ∈
          CFSG.pPrimeCore p ↥(Subgroup.centralizer ({(a : W)} : Set W)) := hN hyN
      rw [hP'C'] at hmem
      have h1 : (⟨y, hy.2⟩ : ↥(Subgroup.centralizer ({(a : W)} : Set W))) = 1 :=
        Subgroup.mem_bot.mp hmem
      exact Subgroup.mem_bot.mpr
        (congrArg (fun z : ↥(Subgroup.centralizer ({(a : W)} : Set W)) => (z : W)) h1)
    have hxbot : (x : W) ∈ (⊥ : Subgroup W) := by
      rw [← hDbot]
      exact hxD
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  have htopbot : (⊤ : Subgroup J) = ⊥ := by
    rw [← hgen, iSup₂_eq_bot]
    exact fun a ha => hfix a ha
  obtain ⟨-, a, b, hab⟩ := ggSporK_components_simple hP' hP hJ
  apply hab
  have ha1 : a = 1 := by
    have hmem : a ∈ (⊥ : Subgroup J) := by rw [← htopbot]; exact Subgroup.mem_top a
    exact Subgroup.mem_bot.mp hmem
  have hb1 : b = 1 := by
    have hmem : b ∈ (⊥ : Subgroup J) := by rw [← htopbot]; exact Subgroup.mem_top b
    exact Subgroup.mem_bot.mp hmem
  rw [ha1, hb1]

private theorem gk4_AJ_ne_bot {W : Type} [Group W] [Finite W] {p : ℕ}
    (hCen : BMNoLiePComp p W) (hG1 : BMPPrimeCore p W) {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat p H E) (hP' : LargeEvenPPrimeCore p ↥H = ⊥)
    (hP : CFSG.pCore p ↥H = ⊥) {e : W} (he : e ∈ E) (he1 : e ≠ 1)
    {K : Subgroup W} (hK : IsComponentOf K H) : gk4_AJ p e K ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hyp.1.1⟩
  have h2 : CFSG.pCore 2 ↥H = ⊥ := ggSporK_pCore_two_eq_bot hyp.1.1 hyp.1.2.1 hP'
  have heord : orderOf e = p := orderOf_eq_prime (hyp.1.2.2.1.2 e he) he1
  obtain ⟨hCH, -, hP'C, hnoComp⟩ := ggSporK_step_one hCen hG1 hyp he he1
  have hKnorm : e ∈ Subgroup.normalizer (K : Set W) := by
    have hEJ := (ggSporK_component_data hyp h2 hK).1
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    constructor
    · intro hx; simpa using hEJ e⁻¹ (E.inv_mem he) x hx
    · intro hx
      have h := hEJ e he (e⁻¹ * x * e) hx
      have heq : e * (e⁻¹ * x * e) * e⁻¹ = x := by group
      rwa [heq] at h
  have hpK : p ∣ Nat.card ↥K := ggSporK_p_dvd_card_component hCen hG1 hyp hP' hP hK
  obtain ⟨u, huK, huord, hue⟩ := gk4_Exists_orderOf_eq_p_centralizes hyp.1.1 hpK heord hKnorm
  have hDne : gk4_DJ e K ≠ ⊥ := by
    intro hbot
    have hmem : u ∈ (⊥ : Subgroup W) := by
      rw [← hbot]
      exact ⟨huK, Subgroup.mem_centralizer_singleton_iff.mpr hue.symm⟩
    have hu1 : u = 1 := Subgroup.mem_bot.mp hmem
    rw [hu1, orderOf_one] at huord
    exact hyp.1.1.ne_one huord.symm
  have hDsub : CFSG.Assembly.IsSubnormal (gk4_DJ e K) (Subgroup.centralizer ({e} : Set W)) :=
    hK.2.1.inf_of_le hCH
  have hYne : (gk4_DJ e K).subgroupOf (Subgroup.centralizer ({e} : Set W)) ≠ ⊥ := by
    intro h
    apply hDne
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.2⟩ : ↥(Subgroup.centralizer ({e} : Set W))) ∈
        (gk4_DJ e K).subgroupOf (Subgroup.centralizer ({e} : Set W)) :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [h] at hx'
    rw [Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  have hYs : ((gk4_DJ e K).subgroupOf (Subgroup.centralizer ({e} : Set W))).IsSubnormal :=
    hDsub.subgroupOf
  have hP'G : CFSG.pPrimeCore p ↥(Subgroup.centralizer ({e} : Set W)) = ⊥ := hP'C
  have hlayerG : CFSG.layer ↥(Subgroup.centralizer ({e} : Set W)) = ⊥ := by
    rw [CFSG.layer.eq_sSup, sSup_eq_bot]
    intro L hL
    exfalso
    refine hnoComp (L.map (Subgroup.centralizer ({e} : Set W)).subtype) ?_
    rw [CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
      (Subgroup.map_subtype_le L)]
    have hsub : (L.map (Subgroup.centralizer ({e} : Set W)).subtype).subgroupOf
        (Subgroup.centralizer ({e} : Set W)) = L := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        rw [Subtype.ext hyx] at hy
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rwa [hsub]
  have hpc : CFSG.pCore p ↥((gk4_DJ e K).subgroupOf (Subgroup.centralizer ({e} : Set W))) ≠ ⊥ :=
    gk4_PCore_ne_bot_of_isSubnormal hP'G hlayerG hYs hYne
  have hiso : ↥((gk4_DJ e K).subgroupOf (Subgroup.centralizer ({e} : Set W))) ≃* ↥(gk4_DJ e K) :=
    Subgroup.subgroupOfEquivOfLe inf_le_right
  have hpc' : CFSG.pCore p ↥(gk4_DJ e K) ≠ ⊥ := by
    intro h
    apply hpc
    have hmap := CFSG.pCore_map_iso p hiso
    rw [h] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ hiso.injective).mp hmap
  have hOne : gk4_OJ p e K ≠ ⊥ := by
    intro h
    apply hpc'
    exact (Subgroup.map_eq_bot_iff_of_injective _ (gk4_DJ e K).subtype_injective).mp h
  haveI hOp : IsPGroup p ↥(gk4_OJ p e K) :=
    (CFSG.pCore_isPGroup (p := p) (G := ↥(gk4_DJ e K))).map (gk4_DJ e K).subtype
  haveI : Nontrivial ↥(gk4_OJ p e K) := (Subgroup.nontrivial_iff_ne_bot _).mpr hOne
  haveI : Group.IsNilpotent ↥(gk4_OJ p e K) := hOp.isNilpotent
  have hcenter : Subgroup.center ↥(gk4_OJ p e K) ≠ ⊥ := Group.IsNilpotent.center_ne_bot _
  have hZne : gk4_ZJ p e K ≠ ⊥ := by
    intro h
    apply hcenter
    exact (Subgroup.map_eq_bot_iff_of_injective _ (gk4_OJ p e K).subtype_injective).mp h
  haveI hZp : IsPGroup p ↥(gk4_ZJ p e K) :=
    hOp.to_le (Subgroup.map_subtype_le (Subgroup.center ↥(gk4_OJ p e K)))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZp
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    rw [hn0, pow_zero] at hn
    haveI : Nontrivial ↥(gk4_ZJ p e K) := (Subgroup.nontrivial_iff_ne_bot _).mpr hZne
    have hlt : 1 < Nat.card ↥(gk4_ZJ p e K) := Finite.one_lt_card
    rw [hn] at hlt
    exact lt_irrefl 1 hlt
  have hpdvd : p ∣ Nat.card ↥(gk4_ZJ p e K) := by
    rw [hn]; exact dvd_pow_self p (ne_of_gt hnpos)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hzord : orderOf (z : W) = p := by rw [Subgroup.orderOf_coe, hz]
  have hzA : (z : W) ∈ gk4_AJ p e K :=
    Subgroup.subset_closure ⟨z.2, by
      have h : orderOf (z : W) ∣ p := by
        have h2 : p = orderOf (z : W) := hzord.symm
        exact h2 ▸ dvd_rfl
      exact (orderOf_dvd_iff_pow_eq_one).mp h⟩
  intro hbot
  have hmem : (z : W) ∈ (⊥ : Subgroup W) := hbot ▸ hzA
  have hz1 : (z : W) = 1 := Subgroup.mem_bot.mp hmem
  have hzord : orderOf (z : W) = p := by rw [Subgroup.orderOf_coe, hz]
  rw [hz1, orderOf_one] at hzord
  exact hyp.1.1.ne_one hzord.symm

theorem ggSporK_component_unique {W : Type} [Group W] [Finite W] {p : ℕ}
    (hCen : BMNoLiePComp p W) (hG1 : BMPPrimeCore p W) (hZ : BMCentreZ p W) {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat p H E) (hP' : LargeEvenPPrimeCore p ↥H = ⊥)
    (hP : CFSG.pCore p ↥H = ⊥) {J J' : Subgroup W} (hJ : IsComponentOf J H)
    (hJ' : IsComponentOf J' H) : J = J' := by
  by_contra hne
  haveI : Fact p.Prime := ⟨hyp.1.1⟩
  have hEnontriv : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hyp.1.2.2.2.1]
    exact Nat.one_lt_pow (by norm_num) hyp.1.1.one_lt
  obtain ⟨e, he1⟩ := exists_ne (1 : E)
  have heE : (e : W) ∈ E := e.2
  have heW1 : (e : W) ≠ 1 := fun h => he1 (Subtype.ext h)
  have heord : orderOf (e : W) = p := orderOf_eq_prime (hyp.1.2.2.1.2 (e : W) heE) heW1
  obtain ⟨hCH, hnoP, hP'C, hnoComp⟩ := ggSporK_step_one hCen hG1 hyp heE heW1
  have hJsimple : IsSimpleGroup ↥J := (ggSporK_components_simple hP' hP hJ).1
  haveI : IsSimpleGroup ↥J := hJsimple
  have hZJ : Subgroup.center ↥J = ⊥ :=
    gk4_Center_eq_bot_of_isSimpleGroup (ggSporK_components_simple hP' hP hJ).2
  have hKJ : CFSG.IsComponent (J.subgroupOf H) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJ.1).mp hJ
  have hKJ' : CFSG.IsComponent (J'.subgroupOf H) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJ'.1).mp hJ'
  have hKne : J.subgroupOf H ≠ J'.subgroupOf H := by
    intro h
    apply hne
    have h' : J ⊓ H = J' ⊓ H := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hJ.1, inf_eq_left.mpr hJ'.1] at h'
  have hcomm : ⁅J, J'⁆ = ⊥ := by
    have h := (CFSG.LocalCores.distinct_components_commute hKJ hKJ').resolve_left hKne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h ⊢
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hx' : (⟨x, hJ.1 hx⟩ : ↥H) ∈ J.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
    have hy' : (⟨y, hJ'.1 hy⟩ : ↥H) ∈ J'.subgroupOf H := Subgroup.mem_subgroupOf.mpr hy
    have hc := h hx'
    rw [Subgroup.mem_centralizer_iff] at hc
    exact congrArg Subtype.val (hc ⟨y, hJ'.1 hy⟩ hy')
  have hdisj : J ⊓ J' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxJ : (⟨x, hx.1⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hJ'c : J' ≤ Subgroup.centralizer (J : Set W) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (by rw [Subgroup.commutator_comm]; exact hcomm)
      exact Subgroup.mem_centralizer_iff.mp (hJ'c hx.2) y y.2
    rw [hZJ] at hxJ
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hxJ))
  let S : Set W := {z : W | ∃ K : Subgroup W, IsComponentOf K H ∧ z ∈ gk4_AJ p (e : W) K}
  let A : Subgroup W := Subgroup.closure S
  have hS_le_cen : S ⊆ (Subgroup.centralizer ({(e : W)} : Set W) : Set W) :=
    fun _ hz => gk4_AJ_le_centralizer p (e : W) hz.choose hz.choose_spec.2
  have hA_le_cen : A ≤ Subgroup.centralizer ({(e : W)} : Set W) :=
    (Subgroup.closure_le _).mpr hS_le_cen
  have hS_elem : IsElemAbelian p A := by
    refine gk4_IsElemAbelian_closure ?_ ?_
    · rintro a ⟨K, hK, ha⟩ b ⟨K', hK', hb⟩
      by_cases hKK' : K = K'
      · subst hKK'
        exact gk4_ZJ_comm p (e : W) K (gk4_AJ_le_ZJ p (e : W) K ha)
          (gk4_AJ_le_ZJ p (e : W) K hb)
      · have hc : ⁅K, K'⁆ = ⊥ := by
          have hK'' : CFSG.IsComponent (K.subgroupOf H) :=
            (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
              hK.1).mp hK
          have hK''' : CFSG.IsComponent (K'.subgroupOf H) :=
            (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
              hK'.1).mp hK'
          have hne' : K.subgroupOf H ≠ K'.subgroupOf H := by
            intro h
            apply hKK'
            have := Subgroup.subgroupOf_inj.mp h
            rwa [inf_eq_left.mpr hK.1, inf_eq_left.mpr hK'.1] at this
          have h0 := (CFSG.LocalCores.distinct_components_commute hK'' hK''').resolve_left hne'
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h0 ⊢
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hx' : (⟨x, hK.1 hx⟩ : ↥H) ∈ K.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
          have hy' : (⟨y, hK'.1 hy⟩ : ↥H) ∈ K'.subgroupOf H := Subgroup.mem_subgroupOf.mpr hy
          have hc := h0 hx'
          rw [Subgroup.mem_centralizer_iff] at hc
          exact congrArg Subtype.val (hc ⟨y, hK'.1 hy⟩ hy')
        have hlive : K ≤ Subgroup.centralizer (K' : Set W) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
        exact (Subgroup.mem_centralizer_iff.mp (hlive (gk4_AJ_le_component p (e : W) K ha)) b
          (gk4_AJ_le_component p (e : W) K' hb)).symm
    · rintro a ⟨K, hK, ha⟩
      exact (gk4_AJ_isElemAbelian p (e : W) K).2 a ha
  have hA_norm : ∀ g ∈ Subgroup.centralizer ({(e : W)} : Set W), ∀ a ∈ A,
      g * a * g⁻¹ ∈ A := by
    intro g hg a ha
    have hgen : ∀ z ∈ S, g * z * g⁻¹ ∈ S := by
      rintro z ⟨K, hK, hz⟩
      exact ⟨K.map (MulAut.conj g).toMonoidHom, gk4_IsComponentOf_map_conj hK (hCH hg),
        (gk4_AJ_map_le p (e : W) g hg K)
          (Subgroup.mem_map.mpr ⟨z, hz, by simp [MulAut.conj_apply]⟩)⟩
    have hle : Subgroup.map (MulAut.conj g).toMonoidHom A ≤ A := by
      rw [Subgroup.map_le_iff_le_comap]
      refine (Subgroup.closure_le _).mpr ?_
      intro z hz
      exact Subgroup.mem_comap.mpr (Subgroup.subset_closure (hgen z hz))
    exact hle (Subgroup.mem_map.mpr ⟨a, ha, by simp [MulAut.conj_apply]⟩)
  have hJ_ne_bot : gk4_AJ p (e : W) J ≠ ⊥ :=
    gk4_AJ_ne_bot hCen hG1 hyp hP' hP heE heW1 hJ
  have hJ'_ne_bot : gk4_AJ p (e : W) J' ≠ ⊥ :=
    gk4_AJ_ne_bot hCen hG1 hyp hP' hP heE heW1 hJ'
  haveI : Nontrivial ↥(gk4_AJ p (e : W) J) := (Subgroup.nontrivial_iff_ne_bot _).mpr hJ_ne_bot
  haveI : Nontrivial ↥(gk4_AJ p (e : W) J') := (Subgroup.nontrivial_iff_ne_bot _).mpr hJ'_ne_bot
  obtain ⟨u, hu1⟩ := exists_ne (1 : ↥(gk4_AJ p (e : W) J))
  obtain ⟨v, hv1⟩ := exists_ne (1 : ↥(gk4_AJ p (e : W) J'))
  have huA : (u : W) ∈ A := Subgroup.subset_closure ⟨J, hJ, u.2⟩
  have hvA : (v : W) ∈ A := Subgroup.subset_closure ⟨J', hJ', v.2⟩
  have huord : orderOf (u : W) = p :=
    orderOf_eq_prime ((gk4_AJ_isElemAbelian p (e : W) J).2 u u.2)
      (fun h => hu1 (Subtype.ext h))
  have hvord : orderOf (v : W) = p :=
    orderOf_eq_prime ((gk4_AJ_isElemAbelian p (e : W) J').2 v v.2)
      (fun h => hv1 (Subtype.ext h))
  have hzu_ne : Subgroup.zpowers (u : W) ≠ Subgroup.zpowers (v : W) := by
    intro heq
    have huv : (u : W) ∈ Subgroup.zpowers (v : W) := by
      rw [← heq]; exact Subgroup.mem_zpowers (u : W)
    have huJ' : (u : W) ∈ J' :=
      (Subgroup.zpowers_le.mpr (gk4_AJ_le_component p (e : W) J' v.2)) huv
    have huZ : (⟨(u : W), gk4_AJ_le_component p (e : W) J u.2⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hJ'c : J' ≤ Subgroup.centralizer (J : Set W) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (by rw [Subgroup.commutator_comm]; exact hcomm)
      exact Subgroup.mem_centralizer_iff.mp (hJ'c huJ') y y.2
    rw [hZJ] at huZ
    have huW1 : (u : W) = 1 := by
      have h := Subgroup.mem_bot.mp huZ
      exact congrArg Subtype.val h
    exact hu1 (Subtype.ext huW1)
  have hAle : A ≤ Subgroup.zpowers (e : W) := hZ (e : W) heord hnoP A hA_le_cen hA_norm hS_elem
  have hzu_eq : Subgroup.zpowers (u : W) = Subgroup.zpowers (e : W) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (hAle huA)) (by
      rw [Nat.card_zpowers, Nat.card_zpowers, huord, heord])
  have hzv_eq : Subgroup.zpowers (v : W) = Subgroup.zpowers (e : W) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (hAle hvA)) (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hvord, heord])
  exact hzu_ne (hzu_eq.trans hzv_eq.symm)

theorem ggSporK_layer_simple {W : Type} [Group W] [Finite W] {p : ℕ}
    (hCen : BMNoLiePComp p W) (hG1 : BMPPrimeCore p W) (hZ : BMCentreZ p W) {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat p H E) (hP' : LargeEvenPPrimeCore p ↥H = ⊥)
    (hP : CFSG.pCore p ↥H = ⊥) (hJ : ∃ J : Subgroup W, IsComponentOf J H) :
    ∃ L : Subgroup W, IsComponentOf L H ∧ IsSimpleGroup ↥L ∧
      (∀ C : Subgroup W, IsComponentOf C H → C = L) ∧ H ⊓ Subgroup.centralizer (L : Set W) = ⊥ ∧
      H ≤ Subgroup.normalizer (L : Set W) := by
  obtain ⟨L, hL⟩ := hJ
  refine ⟨L, hL, (ggSporK_components_simple hP' hP hL).1, ?_, ?_, ?_⟩
  · intro C hC
    exact ggSporK_component_unique hCen hG1 hZ hyp hP' hP hC hL
  · rw [eq_bot_iff]
    intro h hh
    rw [Subgroup.mem_bot]
    refine ggSporK_eq_one_of_centralizes_components hP' hP hh.1 ?_
    intro K hK x hx
    have hKL : K = L := ggSporK_component_unique hCen hG1 hZ hyp hP' hP hK hL
    rw [hKL] at hx
    exact (Subgroup.mem_centralizer_iff.mp hh.2 x hx).symm
  · intro h hh
    have hmap : L.map (MulAut.conj h).toMonoidHom = L :=
      ggSporK_component_unique hCen hG1 hZ hyp hP' hP
        (gk4_IsComponentOf_map_conj hL hh) hL
    exact mem_normalizer_of_map_conj_eq hmap

end CFSG.StandardType.SporadicShape

end
