module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20y
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20ya
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20yb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

open scoped Classical in
@[expose] noncomputable def uc22pwrBar (L : Subgroup G) (a : G) : Bar2 L :=
  if h : a ∈ L then QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨a, h⟩ else 1

theorem uc22pwrBar_of_mem {L : Subgroup G} {a : G} (h : a ∈ L) :
    uc22pwrBar L a = QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨a, h⟩ := by
  unfold uc22pwrBar
  rw [dif_pos h]

theorem uc22pwrBar_mul {L : Subgroup G} {a b : G} (ha : a ∈ L) (hb : b ∈ L) :
    uc22pwrBar L (a * b) = uc22pwrBar L a * uc22pwrBar L b := by
  rw [uc22pwrBar_of_mem (L.mul_mem ha hb), uc22pwrBar_of_mem ha, uc22pwrBar_of_mem hb, ← map_mul]
  rfl

theorem uc22pwrBar_one (L : Subgroup G) : uc22pwrBar L 1 = 1 := by
  rw [uc22pwrBar_of_mem L.one_mem]
  exact map_one _

theorem uc22pwrBar_inv {L : Subgroup G} {a : G} (ha : a ∈ L) :
    uc22pwrBar L a⁻¹ = (uc22pwrBar L a)⁻¹ := by
  rw [uc22pwrBar_of_mem (L.inv_mem ha), uc22pwrBar_of_mem ha, ← map_inv]
  rfl

theorem uc22pwrBar_eq_one_iff {L : Subgroup G} {a : G} (ha : a ∈ L) :
    uc22pwrBar L a = 1 ↔ a ∈ pCoreOf 2 L := by
  rw [uc22pwrBar_of_mem ha, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨⟨a, ha⟩, h, rfl⟩
  · rintro ⟨y, hy, hya⟩
    have : y = ⟨a, ha⟩ := Subtype.ext hya
    rwa [this] at hy

theorem uc22pwrBar_eq_iff {L : Subgroup G} {a b : G} (ha : a ∈ L) (hb : b ∈ L) :
    uc22pwrBar L a = uc22pwrBar L b ↔ a⁻¹ * b ∈ pCoreOf 2 L := by
  rw [← uc22pwrBar_eq_one_iff (L.mul_mem (L.inv_mem ha) hb), uc22pwrBar_mul (L.inv_mem ha) hb,
    uc22pwrBar_inv ha, inv_mul_eq_one]

theorem uc22pwrBar_conj {L : Subgroup G} {t a : G} (ht : t ∈ normalizer (L : Set G)) (ha : a ∈ L) :
    uc22pwrBar L (t * a * t⁻¹) = uc22p20uInd L t ht (uc22pwrBar L a) := by
  have hm : t * a * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 ht a).1 ha
  rw [uc22pwrBar_of_mem hm, uc22pwrBar_of_mem ha]
  exact (uc22p20uInd_mk L ht ⟨a, ha⟩).symm

theorem uc22pwrBar_surj (L : Subgroup G) (x : Bar2 L) : ∃ a ∈ L, uc22pwrBar L a = x := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) x
  exact ⟨l, l.2, uc22pwrBar_of_mem l.2⟩

theorem uc22pwrBar_mem_sylowBar_iff (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) {a : G}
    (ha : a ∈ L) : uc22pwrBar L a ∈ uc22p20iSylowBar D L ↔ a ∈ D.T ⊓ L := by
  rw [uc22pwrBar_of_mem ha]
  exact uc22p20i_mem_sylowBar_iff D hL ⟨a, ha⟩

theorem uc22pwr_exists_of_mem_sylowBar (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    {u : Bar2 L} (hu : u ∈ uc22p20iSylowBar D L) : ∃ s ∈ D.T ⊓ L, uc22pwrBar L s = u := by
  obtain ⟨a, ha, rfl⟩ := uc22pwrBar_surj L u
  exact ⟨a, (uc22pwrBar_mem_sylowBar_iff D hL ha).1 hu, rfl⟩

theorem uc22pwr_isMulCommutative {X : Type*} [Group X] {H : Subgroup X}
    (h : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) : IsMulCommutative H :=
  Subgroup.le_centralizer_iff_isMulCommutative.1 fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => h y hy x hx

structure UC22pwrLift (L : Subgroup G) (F : Subgroup (Bar2 L)) (A : Subgroup G) : Prop where
  le : A ≤ L
  maps : ∀ a ∈ A, uc22pwrBar L a ∈ F
  onto : ∀ f ∈ F, ∃ a ∈ A, uc22pwrBar L a = f
  inj : ∀ a ∈ A, ∀ b ∈ A, uc22pwrBar L a = uc22pwrBar L b → a = b

@[expose] noncomputable def UC22pwrLift.hom {L : Subgroup G} {F : Subgroup (Bar2 L)}
    {A : Subgroup G} (h : UC22pwrLift L F A) : ↥A →* ↥F where
  toFun a := ⟨uc22pwrBar L a, h.maps a a.2⟩
  map_one' := Subtype.ext (uc22pwrBar_one L)
  map_mul' a b := Subtype.ext (uc22pwrBar_mul (h.le a.2) (h.le b.2))

@[expose] noncomputable def UC22pwrLift.equiv {L : Subgroup G} {F : Subgroup (Bar2 L)}
    {A : Subgroup G} (h : UC22pwrLift L F A) : ↥A ≃* ↥F :=
  MulEquiv.ofBijective h.hom
    ⟨fun a b hab => Subtype.ext (h.inj a a.2 b b.2 (congrArg Subtype.val hab)),
      fun f => by
        obtain ⟨a, ha, hf⟩ := h.onto f f.2
        exact ⟨⟨a, ha⟩, Subtype.ext hf⟩⟩

theorem UC22pwrLift.card_eq {L : Subgroup G} {F : Subgroup (Bar2 L)} {A : Subgroup G}
    (h : UC22pwrLift L F A) : Nat.card A = Nat.card F :=
  Nat.card_congr h.equiv.toEquiv

theorem UC22pwrLift.isMulCommutative {L : Subgroup G} {F : Subgroup (Bar2 L)} {A : Subgroup G}
    (h : UC22pwrLift L F A) [hF : IsMulCommutative F] : IsMulCommutative A := by
  refine uc22pwr_isMulCommutative fun x hx y hy => ?_
  refine h.inj _ (A.mul_mem hx hy) _ (A.mul_mem hy hx) ?_
  rw [uc22pwrBar_mul (h.le hx) (h.le hy), uc22pwrBar_mul (h.le hy) (h.le hx)]
  exact Subgroup.mul_comm_of_mem_isMulCommutative F (h.maps x hx) (h.maps y hy)

theorem UC22pwrLift.isCyclic {L : Subgroup G} {F : Subgroup (Bar2 L)} {A : Subgroup G}
    (h : UC22pwrLift L F A) [hF : IsCyclic F] : IsCyclic A :=
  isCyclic_of_surjective (h.equiv.symm : ↥F →* ↥A) h.equiv.symm.surjective

@[expose] def uc22pwrRestrict {L : Subgroup G} {F : Subgroup (Bar2 L)} {A : Subgroup G}
    (h : UC22pwrLift L F A) (F' : Subgroup (Bar2 L)) : Subgroup G where
  carrier := {a | a ∈ A ∧ uc22pwrBar L a ∈ F'}
  mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
    rw [uc22pwrBar_mul (h.le ha.1) (h.le hb.1)]
    exact F'.mul_mem ha.2 hb.2⟩
  one_mem' := ⟨A.one_mem, by
    rw [uc22pwrBar_one]
    exact F'.one_mem⟩
  inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by
    rw [uc22pwrBar_inv (h.le ha.1)]
    exact F'.inv_mem ha.2⟩

theorem UC22pwrLift.restrict {L : Subgroup G} {F : Subgroup (Bar2 L)} {A : Subgroup G}
    (h : UC22pwrLift L F A) {F' : Subgroup (Bar2 L)} (hF' : F' ≤ F) :
    UC22pwrLift L F' (uc22pwrRestrict h F') where
  le := fun a ha => h.le ha.1
  maps := fun a ha => ha.2
  onto := fun f hf => by
    obtain ⟨a, ha, rfl⟩ := h.onto f (hF' hf)
    exact ⟨a, ⟨ha, hf⟩, rfl⟩
  inj := fun a ha b hb hab => h.inj a ha.1 b hb.1 hab

theorem uc22pwr_sylowSq_of_equiv {H K : Type} [Group H] [Group K] [Finite H] [Finite K]
    (e : H ≃* K) {p : ℕ} (hp : p.Prime)
    (h : ∃ P : Sylow p K, Nat.card P = p ^ 2 ∧ ¬ IsCyclic P) :
    ∃ P : Sylow p H, Nat.card P = p ^ 2 ∧ ¬ IsCyclic P := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP2, hPc⟩ := h
  have hf : Function.Surjective (e.symm : K →* H) := e.symm.surjective
  refine ⟨P.mapSurjective hf, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective]
    rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hP2
  · intro hcyc
    rw [Sylow.coe_mapSurjective] at hcyc
    exact hPc (isCyclic_of_surjective (Subgroup.equivMapOfInjective (P : Subgroup K)
      (e.symm : K →* H) e.symm.injective).symm
      (Subgroup.equivMapOfInjective (P : Subgroup K) (e.symm : K →* H) e.symm.injective).symm.surjective)

@[expose] def uc22pwrPre (L : Subgroup G) (F : Subgroup (Bar2 L)) : Subgroup G where
  carrier := {y | y ∈ L ∧ uc22pwrBar L y ∈ F}
  mul_mem' := fun {a b} ha hb => ⟨L.mul_mem ha.1 hb.1, by
    rw [uc22pwrBar_mul ha.1 hb.1]
    exact F.mul_mem ha.2 hb.2⟩
  one_mem' := ⟨L.one_mem, by
    rw [uc22pwrBar_one]
    exact F.one_mem⟩
  inv_mem' := fun {a} ha => ⟨L.inv_mem ha.1, by
    rw [uc22pwrBar_inv ha.1]
    exact F.inv_mem ha.2⟩

theorem uc22pwr_pCoreOf_le_pre (L : Subgroup G) (F : Subgroup (Bar2 L)) :
    pCoreOf 2 L ≤ uc22pwrPre L F := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  refine ⟨z.2, ?_⟩
  have h1 : uc22pwrBar L (z : G) = 1 := (uc22pwrBar_eq_one_iff z.2).2 ⟨z, hz, rfl⟩
  show uc22pwrBar L (z : G) ∈ F
  rw [h1]
  exact F.one_mem

theorem uc22pwr_normal_pCoreOf_pre (L : Subgroup G) (F : Subgroup (Bar2 L)) :
    ((pCoreOf 2 L).subgroupOf (uc22pwrPre L F)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hnL : (n : G) ∈ L := n.2.1
  have hgL : (g : G) ∈ L := g.2.1
  show (g : G) * n * (g : G)⁻¹ ∈ pCoreOf 2 L
  have hconj : (g : G) * n * (g : G)⁻¹ ∈ L := L.mul_mem (L.mul_mem hgL hnL) (L.inv_mem hgL)
  rw [← uc22pwrBar_eq_one_iff hconj, uc22pwrBar_mul (L.mul_mem hgL hnL) (L.inv_mem hgL),
    uc22pwrBar_mul hgL hnL, uc22pwrBar_inv hgL, (uc22pwrBar_eq_one_iff hnL).2 hn]
  simp

theorem uc22pwr_index_pCoreOf_pre (L : Subgroup G) (F : Subgroup (Bar2 L)) :
    ((pCoreOf 2 L).subgroupOf (uc22pwrPre L F)).index = Nat.card F := by
  let φ : ↥(uc22pwrPre L F) →* Bar2 L :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion (fun y hy => hy.1))
  have hφ : ∀ y : ↥(uc22pwrPre L F), φ y = uc22pwrBar L (y : G) := fun y =>
    (uc22pwrBar_of_mem y.2.1).symm
  have hker : φ.ker = (pCoreOf 2 L).subgroupOf (uc22pwrPre L F) := by
    ext y
    rw [MonoidHom.mem_ker, hφ, Subgroup.mem_subgroupOf]
    exact uc22pwrBar_eq_one_iff y.2.1
  have hrange : φ.range = F := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [hφ]
      exact y.2.2
    · intro hx
      obtain ⟨a, ha, rfl⟩ := uc22pwrBar_surj L x
      exact ⟨⟨a, ha, hx⟩, hφ _⟩
  rw [← hker, Subgroup.index_ker, hrange]

theorem uc22pwr_exists_lift (L : Subgroup G) {F : Subgroup (Bar2 L)} (hF : Odd (Nat.card F)) :
    ∃ A : Subgroup G, UC22pwrLift L F A := by
  have hO2 : IsPGroup 2 (pCoreOf 2 L) := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype
  obtain ⟨A, hAY, -, hdisj, hsplit⟩ := uc22pw_exists_complement (uc22pwr_pCoreOf_le_pre L F)
    (uc22pwr_normal_pCoreOf_pre L F) hO2 (by rw [uc22pwr_index_pCoreOf_pre]; exact hF)
  refine ⟨A, ⟨fun a ha => (hAY ha).1, fun a ha => (hAY ha).2, fun f hf => ?_, fun a ha b hb hab => ?_⟩⟩
  · obtain ⟨a, haL, rfl⟩ := uc22pwrBar_surj L f
    have haY : a ∈ (uc22pwrPre L F : Set G) := ⟨haL, hf⟩
    rw [← hsplit] at haY
    obtain ⟨o, ho, b, hb, rfl⟩ := Set.mem_mul.1 haY
    have hoL : o ∈ L := (uc22pwr_pCoreOf_le_pre L F ho).1
    have hbL : b ∈ L := (hAY hb).1
    refine ⟨b, hb, ?_⟩
    rw [uc22pwrBar_mul hoL hbL, (uc22pwrBar_eq_one_iff hoL).2 ho, one_mul]
  · have haL : a ∈ L := (hAY ha).1
    have hbL : b ∈ L := (hAY hb).1
    have h1 : a⁻¹ * b ∈ pCoreOf 2 L := (uc22pwrBar_eq_iff haL hbL).1 hab
    have h2 : a⁻¹ * b = 1 := Subgroup.disjoint_def.1 hdisj h1 (A.mul_mem (A.inv_mem ha) hb)
    exact inv_mul_eq_one.1 h2

theorem UC22pwrLift.le_normalizer (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    {F : Subgroup (Bar2 L)} {A : Subgroup G} (h : UC22pwrLift L F A)
    (hFU : F ≤ normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L))) :
    A ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
  intro a ha
  have hbar : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨a, h.le ha⟩ ∈
      normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)) := by
    have := hFU (h.maps a ha)
    rwa [uc22pwrBar_of_mem (h.le ha)] at this
  exact uc22p20i_mem_normalizer_of_borel D hL ⟨a, h.le ha⟩ hbar

theorem uc22pwr_ind_mem_sup (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    {F : Subgroup (Bar2 L)}
    (hFU : F ≤ normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)))
    {t : G} (ht : t ∈ normalizer (L : Set G)) (htT : t ∈ D.T)
    (hinv : ∀ x ∈ F, uc22p20uInd L t ht x ∈ F ⊔ uc22p20iSylowBar D L) {y : Bar2 L}
    (hy : y ∈ F ⊔ uc22p20iSylowBar D L) : uc22p20uInd L t ht y ∈ F ⊔ uc22p20iSylowBar D L := by
  have hy' : y ∈ ((F ⊔ uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right F _ hFU] at hy'
  obtain ⟨f, hf, u, hu, rfl⟩ := Set.mem_mul.1 hy'
  rw [map_mul]
  exact Subgroup.mul_mem _ (hinv f hf)
    (Subgroup.mem_sup_right ((uc22p20u_ind_sylowBar D hL ht htT u).1 hu))

theorem uc22pwr_mem_sup_iff (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    {F : Subgroup (Bar2 L)} {A : Subgroup G} (h : UC22pwrLift L F A)
    (hFU : F ≤ normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L))) {x : G} :
    x ∈ (D.T ⊓ L) ⊔ A ↔ x ∈ L ∧ uc22pwrBar L x ∈ F ⊔ uc22p20iSylowBar D L := by
  constructor
  · intro hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (h.le_normalizer D hL hFU)] at hx
    obtain ⟨s, hs, a, ha, rfl⟩ := Set.mem_mul.1 hx
    have hsL : s ∈ L := hs.2
    have haL : a ∈ L := h.le ha
    refine ⟨L.mul_mem hsL haL, ?_⟩
    rw [uc22pwrBar_mul hsL haL]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((uc22pwrBar_mem_sylowBar_iff D hL hsL).2 hs))
      (Subgroup.mem_sup_left (h.maps a ha))
  · rintro ⟨hxL, hx⟩
    have hx' : uc22pwrBar L x ∈ ((F ⊔ uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right F _ hFU] at hx'
    obtain ⟨f, hf, u, hu, hfu⟩ := Set.mem_mul.1 hx'
    obtain ⟨a, ha, haf⟩ := h.onto f hf
    obtain ⟨s, hs, hsu⟩ := uc22pwr_exists_of_mem_sylowBar D hL hu
    have haL : a ∈ L := h.le ha
    have hsL : s ∈ L := hs.2
    have hasL : a * s ∈ L := L.mul_mem haL hsL
    have hbar : uc22pwrBar L (a * s) = uc22pwrBar L x := by
      rw [uc22pwrBar_mul haL hsL, haf, hsu]
      exact hfu
    have ho : (a * s)⁻¹ * x ∈ pCoreOf 2 L := (uc22pwrBar_eq_iff hasL hxL).1 hbar
    have hoS : (a * s)⁻¹ * x ∈ D.T ⊓ L := uc22p20i_pCoreOf_le D hL ho
    have hxeq : x = a * (s * ((a * s)⁻¹ * x)) := by group
    rw [hxeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left (Subgroup.mul_mem _ hs hoS))

theorem uc22pwr_T_le_normalizer_sup (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    {F : Subgroup (Bar2 L)} {A : Subgroup G} (h : UC22pwrLift L F A)
    (hFU : F ≤ normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)))
    (hinv : ∀ (t : G) (ht : t ∈ normalizer (L : Set G)), t ∈ D.T → ∀ x ∈ F,
      uc22p20uInd L t ht x ∈ F ⊔ uc22p20iSylowBar D L) :
    D.T ≤ normalizer (((D.T ⊓ L) ⊔ A : Subgroup G) : Set G) := by
  have key : ∀ t ∈ D.T, ∀ x ∈ (D.T ⊓ L) ⊔ A, t * x * t⁻¹ ∈ (D.T ⊓ L) ⊔ A := by
    intro t htT x hx
    have htL : t ∈ normalizer (L : Set G) := hL.1 htT
    obtain ⟨hxL, hxb⟩ := (uc22pwr_mem_sup_iff D hL h hFU).1 hx
    refine (uc22pwr_mem_sup_iff D hL h hFU).2 ⟨(Subgroup.mem_normalizer_iff.1 htL x).1 hxL, ?_⟩
    rw [uc22pwrBar_conj htL hxL]
    exact uc22pwr_ind_mem_sup D hL hFU htL htT (hinv t htL htT) hxb
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key t ht x hx, fun hx => ?_⟩
  have := key t⁻¹ (D.T.inv_mem ht) _ hx
  simpa [mul_assoc] using this

theorem uc22pwr_permutes (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    {F : Subgroup (Bar2 L)} {A : Subgroup G} (h : UC22pwrLift L F A)
    (hFU : F ≤ normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)))
    (hinv : ∀ (t : G) (ht : t ∈ normalizer (L : Set G)), t ∈ D.T → ∀ x ∈ F,
      uc22p20uInd L t ht x ∈ F ⊔ uc22p20iSylowBar D L) :
    Permutes A D.T :=
  uc22pw_permutes_of_split (S := D.T ⊓ L) (T := D.T) (Ê := (D.T ⊓ L) ⊔ A) inf_le_left
    (uc22pwr_T_le_normalizer_sup D hL h hFU hinv)
    (Subgroup.coe_mul_of_right_le_normalizer_left _ _ (h.le_normalizer D hL hFU)).symm

theorem uc22pwr_mem_normalizer_T (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    {F : Subgroup (Bar2 L)} {A : Subgroup G} (h : UC22pwrLift L F A)
    (hFU : F ≤ normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L))) {x : G}
    (hx : x ∈ A)
    (hfix : ∀ (t : G) (ht : t ∈ normalizer (L : Set G)), t ∈ D.T →
      uc22p20uInd L t ht (uc22pwrBar L x) * (uc22pwrBar L x)⁻¹ ∈ uc22p20iSylowBar D L) :
    x ∈ normalizer (D.T : Set G) := by
  have hxL : x ∈ L := h.le hx
  have hxS : x ∈ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := h.le_normalizer D hL hFU hx
  refine uc22pw_mem_normalizer_of_fixed (S := D.T ⊓ L) inf_le_left hxS fun t htT => ?_
  have htL : t ∈ normalizer (L : Set G) := hL.1 htT
  have htxL : t * x * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 htL x).1 hxL
  have hcomL : t * x * t⁻¹ * x⁻¹ ∈ L := L.mul_mem htxL (L.inv_mem hxL)
  have h1 := hfix t htL htT
  rw [← uc22pwrBar_conj htL hxL, ← uc22pwrBar_inv hxL, ← uc22pwrBar_mul htxL (L.inv_mem hxL),
    uc22pwrBar_mem_sylowBar_iff D hL hcomL] at h1
  refine ⟨x⁻¹ * (t * x * t⁻¹ * x⁻¹) * x, (Subgroup.mem_normalizer_iff''.1 hxS _).1 h1, ?_⟩
  group

theorem uc22pwr_normal_subgroupOf_of_comm {X : Type*} [Group X] {E : Subgroup X}
    (hE : IsMulCommutative E) (H : Subgroup X) : (H.subgroupOf E).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hcomm : (g : X) * n = n * g := Subgroup.mul_comm_of_mem_isMulCommutative E g.2 n.2
  have : g * n * g⁻¹ = n := Subtype.ext (by
    show (g : X) * n * (g : X)⁻¹ = n
    rw [hcomm]
    group)
  rw [this]
  exact hn

theorem uc22pwr_piSet_zpowers_subset {L : Subgroup G} {F : Subgroup (Bar2 L)} {A : Subgroup G}
    (h : UC22pwrLift L F A) {N : Subgroup G} (hNA : N ≤ A) {α : Set ℕ} (hN : piSet N ⊆ α) {x : G}
    (hx : x ∈ N) : piSet (Subgroup.zpowers (uc22pwrBar L x)) ⊆ α := by
  intro p hp
  have hxA : x ∈ A := hNA hx
  refine hN ⟨hp.1, ?_⟩
  have h1 : p ∣ orderOf (uc22pwrBar L x) := by
    have := hp.2
    rwa [Nat.card_zpowers] at this
  have h2 : orderOf (uc22pwrBar L x) ∣ orderOf x := by
    have e1 : uc22pwrBar L x = ((h.hom ⟨x, hxA⟩ : ↥F) : Bar2 L) := rfl
    rw [e1, Subgroup.orderOf_coe, ← Subgroup.orderOf_mk (H := A) x hxA]
    exact orderOf_map_dvd h.hom ⟨x, hxA⟩
  exact (h1.trans h2).trans (Subgroup.orderOf_dvd_natCard N hx)

theorem uc22pwr_oPi_le_normalizer (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    {E F : Subgroup (Bar2 L)} {A : Subgroup G} (h : UC22pwrLift L F A) (hFE : F ≤ E)
    (hEab : IsMulCommutative E)
    (hFU : F ≤ normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)))
    (α : Set ℕ)
    (hα : ∀ (t : G) (ht : t ∈ normalizer (L : Set G)), t ∈ D.T → ∀ x ∈ oPi α E,
      uc22p20uInd L t ht x * x⁻¹ ∈ uc22p20iSylowBar D L) :
    oPi α A ≤ normalizer (D.T : Set G) := by
  refine iSup₂_le fun N hN => ?_
  obtain ⟨hNA, -, hNα⟩ := hN
  intro x hx
  have hxA : x ∈ A := hNA hx
  have hmem : uc22pwrBar L x ∈ oPi α E := by
    have hz : Subgroup.zpowers (uc22pwrBar L x) ≤ oPi α E := by
      refine le_iSup₂_of_le (Subgroup.zpowers (uc22pwrBar L x))
        ⟨?_, uc22pwr_normal_subgroupOf_of_comm hEab _, ?_⟩ le_rfl
      · rw [Subgroup.zpowers_le]
        exact hFE (h.maps x hxA)
      · exact uc22pwr_piSet_zpowers_subset h hNA hNα hx
    exact hz (Subgroup.mem_zpowers _)
  exact uc22pwr_mem_normalizer_T D hL h hFU hxA fun t ht htT => hα t ht htT _ hmem

theorem uc22pwr_pCoreOf_le (A : Subgroup G) (p : ℕ) : pCoreOf p A ≤ A := by
  rintro x ⟨z, -, rfl⟩
  exact z.2

theorem uc22pwr_bar_mem_pCoreOf {L : Subgroup G} {F : Subgroup (Bar2 L)} {A : Subgroup G}
    (h : UC22pwrLift L F A) (p : ℕ) {x : G} (hx : x ∈ pCoreOf p A) :
    uc22pwrBar L x ∈ pCoreOf p F := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hz' : h.equiv z ∈ CFSG.pCore p ↥F := by
    rw [← CFSG.pCore_map_iso p h.equiv]
    exact ⟨z, hz, rfl⟩
  exact ⟨h.equiv z, hz', rfl⟩

@[expose] def uc22pwrImage {L : Subgroup G} (W : Subgroup G) (hW : W ≤ L) : Subgroup (Bar2 L) where
  carrier := {y | ∃ w ∈ W, uc22pwrBar L w = y}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, W.mul_mem ha hb, uc22pwrBar_mul (hW ha) (hW hb)⟩
  one_mem' := ⟨1, W.one_mem, uc22pwrBar_one L⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, W.inv_mem ha, uc22pwrBar_inv (hW ha)⟩

theorem uc22pwr_irrOn (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    {F : Subgroup (Bar2 L)} {A : Subgroup G} (h : UC22pwrLift L F A)
    (hFU : F ≤ normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)))
    (hinv : ∀ (t : G) (ht : t ∈ normalizer (L : Set G)), t ∈ D.T → ∀ x ∈ F,
      uc22p20uInd L t ht x ∈ F ⊔ uc22p20iSylowBar D L)
    (hAodd : Odd (Nat.card A)) (p : ℕ)
    (hirr : ∀ W : Subgroup (Bar2 L), W ≤ pCoreOf p F →
      (∀ φ ∈ uc22p20uA D L, ∀ x ∈ W, φ x ∈ W ⊔ uc22p20iSylowBar D L) → W = ⊥ ∨ W = pCoreOf p F) :
    IrrOn (D.T ⊓ normalizer (A : Set G)) (pCoreOf p A) := by
  intro W hWP hWn
  have hPA : pCoreOf p A ≤ A := uc22pwr_pCoreOf_le A p
  have hWA : W ≤ A := hWP.trans hPA
  have hWL : W ≤ L := hWA.trans h.le
  have hle : uc22pwrImage W hWL ≤ pCoreOf p F := by
    rintro _ ⟨w, hw, rfl⟩
    exact uc22pwr_bar_mem_pCoreOf h p (hWP hw)
  have hinvW : ∀ φ ∈ uc22p20uA D L, ∀ x ∈ uc22pwrImage W hWL,
      φ x ∈ uc22pwrImage W hWL ⊔ uc22p20iSylowBar D L := by
    rintro _ ⟨t, ht, htT, rfl⟩ _ ⟨w, hw, rfl⟩
    obtain ⟨s, hs, hst⟩ := uc22pw_exists_mul_mem_normalizer (T := D.T) (S := D.T ⊓ L)
      (Ê := (D.T ⊓ L) ⊔ A) (A := A) (uc22p20u_T_le_normalizer_inf D hL.1)
      (uc22pwr_T_le_normalizer_sup D hL h hFU hinv) D.sylowM.isPGroup.to_inf_left hAodd
      (h.le_normalizer D hL hFU)
      (Subgroup.coe_mul_of_right_le_normalizer_left _ _ (h.le_normalizer D hL hFU)).symm htT
    have hsT : s ∈ D.T := hs.1
    have hsL : s ∈ L := hs.2
    have hn : s * t ∈ D.T ⊓ normalizer (A : Set G) := ⟨D.T.mul_mem hsT htT, hst⟩
    have hwL : w ∈ L := hWL hw
    have hw'W : (s * t) * w * (s * t)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 (hWn hn) w).1 hw
    have hw'L : (s * t) * w * (s * t)⁻¹ ∈ L := hWL hw'W
    have hcalc : t * w * t⁻¹ = s⁻¹ * ((s * t) * w * (s * t)⁻¹) * s := by group
    rw [← uc22pwrBar_conj ht hwL, hcalc,
      uc22pwrBar_mul (L.mul_mem (L.inv_mem hsL) hw'L) hsL, uc22pwrBar_mul (L.inv_mem hsL) hw'L,
      uc22pwrBar_inv hsL]
    have hu : uc22pwrBar L s ∈ uc22p20iSylowBar D L := (uc22pwrBar_mem_sylowBar_iff D hL hsL).2 hs
    have hy : uc22pwrBar L ((s * t) * w * (s * t)⁻¹) ∈ uc22pwrImage W hWL := ⟨_, hw'W, rfl⟩
    have hyN := hFU (h.maps _ (hWA hw'W))
    have h1 := (Subgroup.mem_normalizer_iff''.1 hyN _).1 ((uc22p20iSylowBar D L).inv_mem hu)
    have hexp : (uc22pwrBar L s)⁻¹ * uc22pwrBar L ((s * t) * w * (s * t)⁻¹) * uc22pwrBar L s =
        uc22pwrBar L ((s * t) * w * (s * t)⁻¹) *
          ((uc22pwrBar L ((s * t) * w * (s * t)⁻¹))⁻¹ * (uc22pwrBar L s)⁻¹ *
            uc22pwrBar L ((s * t) * w * (s * t)⁻¹)) * uc22pwrBar L s := by group
    rw [hexp]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hy)
      (Subgroup.mem_sup_right h1)) (Subgroup.mem_sup_right hu)
  rcases hirr _ hle hinvW with hbot | htop
  · left
    refine (Subgroup.eq_bot_iff_forall W).2 fun w hw => ?_
    have hb : uc22pwrBar L w ∈ uc22pwrImage W hWL := ⟨w, hw, rfl⟩
    rw [hbot] at hb
    have h2 : uc22pwrBar L w = uc22pwrBar L 1 := by
      rw [uc22pwrBar_one]
      exact Subgroup.mem_bot.1 hb
    exact h.inj w (hWA hw) 1 A.one_mem h2
  · right
    refine le_antisymm hWP fun x hx => ?_
    have hxb : uc22pwrBar L x ∈ uc22pwrImage W hWL := by
      rw [htop]
      exact uc22pwr_bar_mem_pCoreOf h p hx
    obtain ⟨w, hw, hwx⟩ := hxb
    have h3 : w = x := h.inj w (hWA hw) x (hPA hx) hwx
    rw [← h3]
    exact hw

theorem uc22pwr_le_normalizer_of_comm {X : Type*} [Group X] {E : Subgroup X}
    (hE : IsMulCommutative E) {H K : Subgroup X} (hH : H ≤ E) (hK : K ≤ E) :
    H ≤ normalizer (K : Set X) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro c
  have hcomm : ∀ k ∈ K, b * k * b⁻¹ = k := fun k hk => by
    rw [Subgroup.mul_comm_of_mem_isMulCommutative E (hH hb) (hK hk)]
    group
  refine ⟨fun hc => by rw [hcomm c hc]; exact hc, fun hc => ?_⟩
  have h1 := hcomm _ hc
  have h2 : c = b * c * b⁻¹ := by
    have := congrArg (fun z => b⁻¹ * z * b) h1
    simpa [mul_assoc] using this.symm
  rw [h2]
  exact hc

theorem uc22pw_lift_sel (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) {n : ℕ} {E : Subgroup (Bar2 L)} (hE : uc22pwGood D L n E)
    {Bb Cb : Subgroup (Bar2 L)} (hBE : Bb ≤ E) (hCE : Cb ≤ E) (hcyc : IsCyclic Bb)
    (hsqf : Squarefree (Nat.card Bb))
    (hBinv : ∀ φ ∈ uc22p20uA D L, ∀ x ∈ Bb, φ x ∈ Bb ⊔ uc22p20iSylowBar D L)
    (hCinv : ∀ φ ∈ uc22p20uA D L, ∀ x ∈ Cb, φ x ∈ Cb ⊔ uc22p20iSylowBar D L)
    (hpiBC : piSet (Bb ⊔ Cb) = piSet E)
    (hCsyl : ∀ p : ℕ, p.Prime → p ∣ Nat.card Cb → ∃ P : Sylow p Cb, Nat.card P = p ^ 2 ∧ ¬ IsCyclic P)
    (hCirr : ∀ p : ℕ, p.Prime → p ∣ Nat.card Cb → ∀ W : Subgroup (Bar2 L), W ≤ pCoreOf p (Bb ⊔ Cb) →
      (∀ φ ∈ uc22p20uA D L, ∀ x ∈ W, φ x ∈ W ⊔ uc22p20iSylowBar D L) → W = ⊥ ∨ W = pCoreOf p (Bb ⊔ Cb)) :
    ∃ B0 : Subgroup G, UC22pwrLift L (Bb ⊔ Cb) B0 ∧ B0 ∈ calB1 D.T D.M L ∧ piSet B0 = etaSet n ∧
      AlphaCond D.T B0 n ∧ B0 ≤ D.M := by
  obtain ⟨hEU, hEab, hEodd, -, hpi, -, hα, w, hw2, hwinv, hgen⟩ := hE
  haveI : IsCyclic ↥Bb := hcyc
  have hE₀E : Bb ⊔ Cb ≤ E := sup_le hBE hCE
  have hE₀U := hE₀E.trans hEU
  have hBU := hBE.trans hEU
  have hCU := hCE.trans hEU
  haveI hE₀ab : IsMulCommutative ↥(Bb ⊔ Cb) := uc22pwr_isMulCommutative fun x hx y hy =>
    Subgroup.mul_comm_of_mem_isMulCommutative E (hE₀E hx) (hE₀E hy)
  haveI hCab : IsMulCommutative ↥Cb := uc22pwr_isMulCommutative fun x hx y hy =>
    Subgroup.mul_comm_of_mem_isMulCommutative E (hCE hx) (hCE hy)
  have hE₀odd : Odd (Nat.card ↥(Bb ⊔ Cb)) := Odd.of_dvd_nat hEodd (Subgroup.card_dvd_of_le hE₀E)
  have hBinv' : ∀ (t : G) (ht : t ∈ normalizer (L : Set G)), t ∈ D.T → ∀ x ∈ Bb,
      uc22p20uInd L t ht x ∈ Bb ⊔ uc22p20iSylowBar D L := fun t ht htT x hx =>
    hBinv _ ⟨t, ht, htT, rfl⟩ x hx
  have hCinv' : ∀ (t : G) (ht : t ∈ normalizer (L : Set G)), t ∈ D.T → ∀ x ∈ Cb,
      uc22p20uInd L t ht x ∈ Cb ⊔ uc22p20iSylowBar D L := fun t ht htT x hx =>
    hCinv _ ⟨t, ht, htT, rfl⟩ x hx
  have hE₀inv : ∀ (t : G) (ht : t ∈ normalizer (L : Set G)), t ∈ D.T → ∀ x ∈ Bb ⊔ Cb,
      uc22p20uInd L t ht x ∈ (Bb ⊔ Cb) ⊔ uc22p20iSylowBar D L := by
    intro t ht htT x hx
    have hx' : x ∈ ((Bb ⊔ Cb : Subgroup (Bar2 L)) : Set (Bar2 L)) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Bb Cb
      (uc22pwr_le_normalizer_of_comm hEab hBE hCE)] at hx'
    obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_mul.1 hx'
    rw [map_mul]
    exact Subgroup.mul_mem _
      (sup_le_sup_right (le_sup_left : Bb ≤ Bb ⊔ Cb) _ (hBinv' t ht htT b hb))
      (sup_le_sup_right (le_sup_right : Cb ≤ Bb ⊔ Cb) _ (hCinv' t ht htT c hc))
  obtain ⟨A, hA⟩ := uc22pwr_exists_lift L hE₀odd
  have hAodd : Odd (Nat.card A) := by
    rw [hA.card_eq]
    exact hE₀odd
  have hBl := hA.restrict (le_sup_left : Bb ≤ Bb ⊔ Cb)
  have hCl := hA.restrict (le_sup_right : Cb ≤ Bb ⊔ Cb)
  have hinvA : ∀ a : ↥L, (a : G) ∈ A → w * QuotientGroup.mk a * w⁻¹ = (QuotientGroup.mk a)⁻¹ := by
    intro a ha
    have h1 := hwinv _ (hE₀E (hA.maps _ ha))
    rwa [uc22pwrBar_of_mem a.2] at h1
  obtain ⟨r, ⟨k, hk⟩, hrw, hrinv⟩ := uc22pw_exists_inverting hA.le hAodd w hw2 hinvA
  have hrM : (r : G) ∉ D.M := by
    refine uc22pw_not_mem_M D hB h1930 hL (r := r) ?_
    rw [hrw]
    exact hgen
  refine ⟨A, hA, ⟨hA.le, hA.isMulCommutative, uc22pwrRestrict hA Bb, uc22pwrRestrict hA Cb,
    ⟨hBl.le, hBl.isCyclic, ?_, ?_, ?_, ⟨r, r.2, hrM, ⟨k, hk⟩, fun x hx => hrinv x hx.1⟩⟩,
    hCl.isMulCommutative, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hBl.card_eq]
    exact hsqf
  · rw [hBl.card_eq]
    exact Odd.of_dvd_nat hEodd (Subgroup.card_dvd_of_le hBE)
  · exact uc22pwr_permutes D hL hBl hBU hBinv'
  · rw [hCl.card_eq]
    exact Odd.of_dvd_nat hEodd (Subgroup.card_dvd_of_le hCE)
  · intro p hp hpc
    rw [hCl.card_eq] at hpc
    exact uc22pwr_sylowSq_of_equiv hCl.equiv hp (hCsyl p hp hpc)
  ·
    refine le_antisymm (fun a ha => ?_) (sup_le (fun x hx => hx.1) (fun x hx => hx.1))
    have hab := hA.maps a ha
    have hab' : uc22pwrBar L a ∈ ((Bb ⊔ Cb : Subgroup (Bar2 L)) : Set (Bar2 L)) := hab
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Bb Cb
      (uc22pwr_le_normalizer_of_comm hEab hBE hCE)] at hab'
    obtain ⟨b, hb, c, hc, hbc⟩ := Set.mem_mul.1 hab'
    obtain ⟨b', hb', hb'e⟩ := hBl.onto b hb
    obtain ⟨c', hc', hc'e⟩ := hCl.onto c hc
    have hbA : b' ∈ A := hb'.1
    have hcA : c' ∈ A := hc'.1
    have hbc' : b' * c' = a := hA.inj _ (A.mul_mem hbA hcA) a ha (by
      rw [uc22pwrBar_mul (hA.le hbA) (hA.le hcA), hb'e, hc'e, hbc])
    rw [← hbc']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb') (Subgroup.mem_sup_right hc')
  · exact uc22pwr_permutes D hL hA hE₀U hE₀inv
  · exact ⟨r, r.2, hrM, ⟨k, hk⟩, hrinv⟩
  · intro p hp hpc
    rw [hCl.card_eq] at hpc
    exact uc22pwr_irrOn D hL hA hE₀U hE₀inv hAodd p (hCirr p hp hpc)
  · have hcard : piSet A = piSet (Bb ⊔ Cb) := by
      unfold piSet
      rw [hA.card_eq]
    rw [hcard, hpiBC, hpi]
  · intro e m hm hnm
    exact uc22pwr_oPi_le_normalizer D hL hA hE₀E hEab hE₀U _ (hα e m hm hnm)
  · intro a ha
    have hbar : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨a, hA.le ha⟩ ∈
        normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)) := by
      have := hE₀U (hA.maps a ha)
      rwa [uc22pwrBar_of_mem (hA.le ha)] at this
    exact uc22p20i_borel_le_M D hB h1930 hL ⟨a, hA.le ha⟩ hbar

theorem uc22pw_lift (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) {n : ℕ} {E : Subgroup (Bar2 L)} (hE : uc22pwGood D L n E) :
    ∃ B0 : Subgroup G, B0 ∈ calB1 D.T D.M L ∧ piSet B0 = etaSet n ∧ AlphaCond D.T B0 n ∧
      B0 ≤ D.M := by
  obtain ⟨hEU, hEab, hEodd, hrank, -, hinv, -⟩ := id hE
  have hΦU : ∀ φ ∈ uc22p20uA D L, ∀ x : Bar2 L,
      x ∈ uc22p20iSylowBar D L ↔ φ x ∈ uc22p20iSylowBar D L := by
    rintro _ ⟨t, ht, htT, rfl⟩ x
    exact uc22p20u_ind_sylowBar D hL ht htT x
  have hΦE : ∀ φ ∈ uc22p20uA D L, ∀ x ∈ E, φ x ∈ E ⊔ uc22p20iSylowBar D L := by
    rintro _ ⟨t, ht, htT, rfl⟩ x hx
    exact hinv t ht htT x hx
  obtain ⟨Bb, Cb, hBE, hCE, -, hcyc, hsqf, hBinv, hCinv, hpiBC, hCsyl, hCirr⟩ :=
    uc22pw_select_mod hEU (uc22p20i_sylowBar_isPGroup D) hEab hEodd hrank (uc22p20uA D L) hΦU hΦE
  obtain ⟨B0, -, hB0⟩ :=
    uc22pw_lift_sel D hB h1930 hL hE hBE hCE hcyc hsqf hBinv hCinv hpiBC hCsyl hCirr
  exact ⟨B0, hB0⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
