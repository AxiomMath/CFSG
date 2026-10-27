module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch4Sec3L4313
public import CFSG.Quasithin.Vol2.Ch4Sec3L4314R

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat
open scoped MatrixGroups Pointwise

namespace L4315

@[expose] noncomputable def autModO2 (L : Type) [Group L] :
    MulAut L →* MulAut (L ⧸ CFSG.pCore 2 L) where
  toFun φ := QuotientGroup.congr (CFSG.pCore 2 L) (CFSG.pCore 2 L) φ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

variable {G : Type} [Group G]

@[expose] noncomputable def conjModO2 (L : Subgroup G) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut (ModO2 L) :=
  (autModO2 ↥L).comp L.normalizerMonoidHom

theorem conjModO2_mk (L : Subgroup G) (g : ↥(Subgroup.normalizer (L : Set G))) (k : ↥L) :
    conjModO2 L g (QuotientGroup.mk k) =
      QuotientGroup.mk (⟨(g : G) * k * (g : G)⁻¹, (g.2 k).mp k.2⟩ : ↥L) := rfl

theorem commutator_mem_of_conjModO2_eq_one {L : Subgroup G}
    {g : ↥(Subgroup.normalizer (L : Set G))} (hg : conjModO2 L g = 1) {k : G} (hk : k ∈ L) :
    (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 L := by
  have hNn : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have h1 := congrArg (fun φ : MulAut (ModO2 L) => φ (QuotientGroup.mk (⟨k⁻¹, L.inv_mem hk⟩ : ↥L)))
    hg
  simp only [conjModO2_mk, MulAut.one_apply] at h1
  rw [QuotientGroup.eq] at h1
  have h2 : (⟨(g : G) * k⁻¹ * (g : G)⁻¹, (g.2 _).mp (L.inv_mem hk)⟩ : ↥L)⁻¹ *
      (⟨k⁻¹, L.inv_mem hk⟩ : ↥L) = ⟨(g : G) * k * (g : G)⁻¹ * k⁻¹,
        L.mul_mem ((g.2 k).mp hk) (L.inv_mem hk)⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [h2] at h1
  exact (mem_pCoreOf_iff' _).mpr h1

theorem conjModO2_of_mem (L : Subgroup G) (k : ↥L) :
    conjModO2 L ⟨(k : G), Subgroup.le_normalizer k.2⟩ =
      MulAut.conj (QuotientGroup.mk k : ModO2 L) := by
  ext x
  induction x using QuotientGroup.induction_on
  rfl

theorem eq_one_of_commute_conj {Q : Type} [Group Q] (hperf : commutator Q = ⊤) (φ : MulAut Q)
    (h : ∀ q : Q, φ * MulAut.conj q = MulAut.conj q * φ) : φ = 1 := by
  have hc : ∀ q : Q, q⁻¹ * φ q ∈ Subgroup.center Q := by
    intro q
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 := congrArg (fun ψ : MulAut Q => ψ (φ.symm x)) (h q)
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at h1
    calc x * (q⁻¹ * φ q) = q⁻¹ * (q * x * q⁻¹) * φ q := by group
      _ = q⁻¹ * (φ q * x * (φ q)⁻¹) * φ q := by rw [h1]
      _ = q⁻¹ * φ q * x := by group
  let f : Q →* ↥(Subgroup.center Q) :=
    { toFun := fun q => ⟨q⁻¹ * φ q, hc q⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show (a * b)⁻¹ * φ (a * b) = a⁻¹ * φ a * (b⁻¹ * φ b)
        have hca : b⁻¹ * (a⁻¹ * φ a) = a⁻¹ * φ a * b⁻¹ := Subgroup.mem_center_iff.mp (hc a) b⁻¹
        rw [map_mul, mul_inv_rev]
        calc b⁻¹ * a⁻¹ * (φ a * φ b) = b⁻¹ * (a⁻¹ * φ a) * φ b := by group
          _ = a⁻¹ * φ a * b⁻¹ * φ b := by rw [hca]
          _ = a⁻¹ * φ a * (b⁻¹ * φ b) := by group) }
  have hker : commutator Q ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [hperf] at hker
  ext q
  have hq : f q = 1 := hker (Subgroup.mem_top q)
  have h1 : q⁻¹ * φ q = 1 := congrArg Subtype.val hq
  rw [MulAut.one_apply]
  calc φ q = q * (q⁻¹ * φ q) := by group
    _ = q := by rw [h1, mul_one]

theorem ker_conj (Q : Type) [Group Q] :
    (MulAut.conj : Q →* MulAut Q).ker = Subgroup.center Q := by
  ext q
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have h1 := congrArg (fun φ : MulAut Q => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * q = q * g * q⁻¹ * q := by rw [h1]
      _ = q * g := by group
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h g]
    group

@[expose] noncomputable def innEquiv (Q : Type) [Group Q] :
    Q ⧸ Subgroup.center Q ≃* ↥(MulAut.conj : Q →* MulAut Q).range :=
  (QuotientGroup.quotientMulEquivOfEq (ker_conj Q).symm).trans
    (QuotientGroup.quotientKerEquivRange _)

theorem isSimpleGroup_inn {Q : Type} [Group Q] (h : IsSimpleGroup (Q ⧸ Subgroup.center Q)) :
    IsSimpleGroup ↥(MulAut.conj : Q →* MulAut Q).range := by
  have := h
  exact (innEquiv Q).symm.isSimpleGroup

theorem exists_not_comm_inn {Q : Type} [Group Q]
    (h : ∃ a b : Q ⧸ Subgroup.center Q, a * b ≠ b * a) :
    ∃ a b : ↥(MulAut.conj : Q →* MulAut Q).range, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨innEquiv Q a, innEquiv Q b, fun h' => hab ?_⟩
  apply (innEquiv Q).injective
  rw [map_mul, map_mul, h']

theorem le_pCoreOf_of_central {G : Type} [Group G] {L A : Subgroup G} (hAL : A ≤ L)
    (hAperf : ⁅A, A⁆ = A)
    (hc : ∀ a (ha : a ∈ A), (QuotientGroup.mk ⟨a, hAL ha⟩ : ModO2 L) ∈ Subgroup.center (ModO2 L)) :
    A ≤ pCoreOf 2 L := by
  have hNn : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  let f : ↥A →* ↥(Subgroup.center (ModO2 L)) :=
    { toFun := fun a => ⟨QuotientGroup.mk ⟨a, hAL a.2⟩, hc a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hA : commutator ↥A = ⊤ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_subtype_commutator, hAperf, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hker : commutator ↥A ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [hA] at hker
  intro a ha
  have h1 : f ⟨a, ha⟩ = 1 := hker (Subgroup.mem_top _)
  have h2 : (QuotientGroup.mk ⟨a, hAL ha⟩ : ModO2 L) = 1 := congrArg Subtype.val h1
  rw [QuotientGroup.eq_one_iff] at h2
  exact (mem_pCoreOf_iff' _).mpr h2

theorem le_of_perfect_of_le_sup {G : Type} [Group G] {A B P : Subgroup G}
    (hAperf : ⁅A, A⁆ = A) (hBA : B ≤ A) (hP : Group.IsSolvable ↥P)
    (hPB : P ≤ Subgroup.normalizer (B : Set G)) (hAle : A ≤ B ⊔ P) : A ≤ B := by
  have hBP : (B : Set G) * (P : Set G) = ((B ⊔ P : Subgroup G) : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left B P hPB).symm
  have hdec : ∀ a ∈ A, ∃ b ∈ B, ∃ p ∈ P, a = b * p := by
    intro a ha
    have : a ∈ (B : Set G) * (P : Set G) := by
      rw [hBP]
      exact hAle ha
    obtain ⟨b, hb, p, hp, rfl⟩ := this
    exact ⟨b, hb, p, hp, rfl⟩
  have hAN : A ≤ Subgroup.normalizer (B : Set G) := by
    intro a ha
    obtain ⟨b, hb, p, hp, rfl⟩ := hdec a ha
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hb) (hPB hp)
  have hn : (B.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBA).mpr hAN
  let ψ : ↥((P ⊓ A).subgroupOf A) →* ↥A ⧸ B.subgroupOf A :=
    (QuotientGroup.mk' (B.subgroupOf A)).comp ((P ⊓ A).subgroupOf A).subtype
  have hψ : Function.Surjective ψ := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨b, hb, p, hp, he⟩ := hdec a a.2
      have hpA : p ∈ A := by
        have : p = b⁻¹ * a := by rw [he]; group
        rw [this]
        exact A.mul_mem (A.inv_mem (hBA hb)) a.2
      refine ⟨⟨⟨p, hpA⟩, ⟨hp, hpA⟩⟩, ?_⟩
      show (QuotientGroup.mk ⟨p, hpA⟩ : ↥A ⧸ B.subgroupOf A) = QuotientGroup.mk a
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : ((⟨p, hpA⟩⁻¹ * a : ↥A) : G) = p⁻¹ * b * p⁻¹⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, he]
        group
      rw [this]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hPB hp)) b).mp hb
  have hsolvPA : Group.IsSolvable ↥((P ⊓ A).subgroupOf A) := by
    let f : ↥((P ⊓ A).subgroupOf A) →* ↥P :=
      { toFun := fun x => ⟨((x : ↥A) : G), x.2.1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y hxy => ?_
    have h1 : ((x : ↥A) : G) = ((y : ↥A) : G) := congrArg (fun z : ↥P => (z : G)) hxy
    exact Subtype.ext (Subtype.ext h1)
  have hsolv : Group.IsSolvable (↥A ⧸ B.subgroupOf A) := Group.isSolvable_of_surjective hψ
  have hA : commutator ↥A = ⊤ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_subtype_commutator, hAperf, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hφs : Function.Surjective (QuotientGroup.mk' (B.subgroupOf A)) :=
    QuotientGroup.mk'_surjective _
  have hperfQ : ⁅(⊤ : Subgroup (↥A ⧸ B.subgroupOf A)), (⊤ : Subgroup (↥A ⧸ B.subgroupOf A))⁆ =
      (⊤ : Subgroup (↥A ⧸ B.subgroupOf A)) := by
    rw [← Subgroup.map_top_of_surjective _ hφs, ← Subgroup.map_commutator, ← commutator_def, hA]
  have : Group.IsSolvable ↥(⊤ : Subgroup (↥A ⧸ B.subgroupOf A)) :=
    Group.isSolvable_of_isSolvable_injective (f := (⊤ : Subgroup (↥A ⧸ B.subgroupOf A)).subtype)
      Subtype.coe_injective
  have htop := CFSG.LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable hperfQ
  intro a ha
  have h1 : (QuotientGroup.mk ⟨a, ha⟩ : ↥A ⧸ B.subgroupOf A) = 1 := by
    have : (QuotientGroup.mk ⟨a, ha⟩ : ↥A ⧸ B.subgroupOf A) ∈
        (⊤ : Subgroup (↥A ⧸ B.subgroupOf A)) := Subgroup.mem_top _
    rw [htop] at this
    exact this
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

end L4315

variable {G : Type} [Group G] [Finite G]

structure Setting4315 (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ)
    (I H K : Subgroup G) (t : G) (m : ℕ) (F : Type) [Field F] [Fintype F]
    (α : ↥K →* ↥(StatedSL 3 F)) (β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F))
    (W' : Submodule F (Fin 3 → F)) (ZS K₂ R₂ : Subgroup G) (μ : Fˣ) (y : G)
    (KZ : Subgroup G) : Prop extends Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y where
  KZ_mem : KZ ∈ cComp (Subgroup.normalizer (ZS : Set G))
  KZ_normal : Subgroup.normalizer (ZS : Set G) ≤ Subgroup.normalizer (KZ : Set G)
  K₂_le_KZ : K₂ ≤ KZ
  KZ_cent : KZ ≤ Subgroup.centralizer (ZS : Set G)
  N_R₂ : Subgroup.normalizer (R₂ : Set G) ≤ H ⊓ Subgroup.normalizer (K₂ : Set G)
  O2_le : pCoreOf 2 (KZ ⊔ T) ≤ R₂
  R₂_eq_P₀ : R₂ = ((radE0 F).comap α).map K.subtype

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem isPGroup_R₂ : IsPGroup 2 ↥R₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [s.R₂_eq]
  exact pCoreOf_isPGroup 2 _

theorem le_normalizer_R₂ : K₂ ⊔ T ⊓ H ≤ Subgroup.normalizer (R₂ : Set G) := by
  rw [s.R₂_eq]
  exact le_normalizer_pCoreOf 2 _

theorem R₂_le_sup : R₂ ≤ K₂ ⊔ T ⊓ H := by
  rw [s.R₂_eq]
  exact pCoreOf_le 2 _

theorem R₂_le_normalizer_K₂ : R₂ ≤ Subgroup.normalizer (K₂ : Set G) :=
  s.R₂_le_sup.trans (_root_.sup_le (fun _ hk => Subgroup.le_normalizer hk) s.S_le_normalizer_K₂)

theorem pCoreOf_KZ_le : pCoreOf 2 KZ ≤ R₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_trans ?_ s.O2_le
  refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 KZ).trans le_sup_left)
    (_root_.sup_le (le_normalizer_pCoreOf 2 KZ) ?_) (pCoreOf_isPGroup 2 KZ)
  exact (s.T_le_normalizer_ZS.trans s.KZ_normal).trans (normalizer_le_normalizer_pCoreOf 2 KZ)

omit s in
@[expose] def G₀ (_s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ) : Subgroup G :=
  KZ ⊔ R₂ ⊔ Subgroup.zpowers y

theorem KZ_le_G₀ : KZ ≤ s.G₀ := le_sup_left.trans le_sup_left

theorem R₂_le_G₀ : R₂ ≤ s.G₀ := le_sup_right.trans le_sup_left

theorem y_mem_G₀ : y ∈ s.G₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

theorem K₂_le_G₀ : K₂ ≤ s.G₀ := s.K₂_le_KZ.trans s.KZ_le_G₀

theorem G₀_le_normalizer_ZS : s.G₀ ≤ Subgroup.normalizer (ZS : Set G) := by
  refine _root_.sup_le (_root_.sup_le (s.KZ_cent.trans
    (Subgroup.centralizer_le_normalizer _)) ?_) s.Y_le_normalizer_ZS
  refine s.R₂_le_sup.trans (_root_.sup_le (s.K₂_le_centralizer.trans
    (Subgroup.centralizer_le_normalizer _)) ?_)
  exact fun x hx => s.T_le_normalizer_ZS hx.1

theorem G₀_le_normalizer_KZ : s.G₀ ≤ Subgroup.normalizer (KZ : Set G) :=
  s.G₀_le_normalizer_ZS.trans s.KZ_normal

@[expose] noncomputable def rho : ↥s.G₀ →* MulAut (ModO2 KZ) :=
  (L4315.conjModO2 KZ).comp (Subgroup.inclusion s.G₀_le_normalizer_KZ)

@[expose] noncomputable def C₀ : Subgroup G := (s.rho.ker).map s.G₀.subtype

theorem mem_C₀ {g : G} (hg : g ∈ s.C₀) {k : G} (hk : k ∈ KZ) :
    g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 KZ := by
  obtain ⟨g', hg', rfl⟩ := hg
  exact L4315.commutator_mem_of_conjModO2_eq_one (g := Subgroup.inclusion s.G₀_le_normalizer_KZ g')
    hg' hk

theorem le_normalizer_C₀ : s.G₀ ≤ Subgroup.normalizer (s.C₀ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ s.G₀, ∀ x ∈ s.C₀, g * x * g⁻¹ ∈ s.C₀ := by
    intro g hg x hx
    obtain ⟨x', hx', rfl⟩ := hx
    refine ⟨⟨g, hg⟩ * x' * (⟨g, hg⟩ : ↥s.G₀)⁻¹, ?_, rfl⟩
    refine MonoidHom.mem_ker.mpr ?_
    rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hx', mul_one, mul_inv_cancel]
  intro x
  refine ⟨key g hg x, fun h => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ h
  simpa [mul_assoc] using this

theorem isSylowTwoOf_R₂_sup (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : IsSylowTwoOf R₂ (R₂ ⊔ s.C₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRC : R₂ ≤ Subgroup.normalizer (s.C₀ : Set G) := s.R₂_le_G₀.trans s.le_normalizer_C₀
  refine isSylowTwoOf_iff_maximal.mpr ⟨le_sup_left, s.isPGroup_R₂, fun P hP hP2 hRP => ?_⟩
  by_contra hPR
  have hlt : R₂ < P := lt_of_le_of_ne hRP fun h => hPR (h ▸ le_rfl)
  obtain ⟨w, hwP, hwN, hwR⟩ := A4.exists_mem_normalizer_not_mem hP2 hlt
  apply hwR
  have hw1 := s.N_R₂ hwN
  rw [s.R₂_eq_P₀] at hwN ⊢
  refine s.mem_P₀_of h135 hR hC h37 h38 h39 hw1.1 ?_ hwN fun k hk => ?_
  · obtain ⟨a, ha⟩ := hP2 ⟨w, hwP⟩
    exact ⟨a, by simpa using congrArg Subtype.val ha⟩
  ·
    have hw' : w ∈ (R₂ : Set G) * (s.C₀ : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right R₂ s.C₀ hRC]
      exact hP hwP
    obtain ⟨r, hr, c, hc, rfl⟩ := hw'
    have hkKZ : k ∈ KZ := s.K₂_le_KZ hk
    have hcomm := s.mem_C₀ hc hkKZ
    have hOR := s.pCoreOf_KZ_le
    have hrK : r ∈ Subgroup.normalizer (K₂ : Set G) := s.R₂_le_normalizer_K₂ hr
    have hkR : k ∈ Subgroup.normalizer (R₂ : Set G) := s.le_normalizer_R₂ (Subgroup.mem_sup_left hk)
    have h1 : r * c * k * (r * c)⁻¹ * k⁻¹ ∈ R₂ := by
      have e : r * c * k * (r * c)⁻¹ * k⁻¹ =
          r * (c * k * c⁻¹ * k⁻¹) * (k * r⁻¹ * k⁻¹) := by group
      rw [e]
      refine R₂.mul_mem (R₂.mul_mem hr (hOR hcomm)) ?_
      exact (Subgroup.mem_normalizer_iff.mp hkR r⁻¹).mp (R₂.inv_mem hr)
    have h2 : r * c * k * (r * c)⁻¹ * k⁻¹ ∈ K₂ :=
      K₂.mul_mem ((Subgroup.mem_normalizer_iff.mp hw1.2 k).mp hk) (K₂.inv_mem hk)
    have hRK : R₂ ⊓ K₂ ≤ pCoreOf 2 K₂ :=
      le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun _ hk => mem_normalizer_inf (s.le_normalizer_R₂ (Subgroup.mem_sup_left hk))
          (Subgroup.le_normalizer hk)) (s.isPGroup_R₂.to_le inf_le_left)
    exact s.pCoreOf_K₂_le_P₀ (hRK ⟨h1, h2⟩)

theorem rho_mem_normalizer_map {A : Subgroup G} {z : G} (hz : z ∈ s.G₀)
    (hzA : z ∈ Subgroup.normalizer (A : Set G)) :
    s.rho ⟨z, hz⟩ ∈ Subgroup.normalizer (((A.subgroupOf s.G₀).map s.rho : Subgroup _) : Set _) := by
  refine Subgroup.le_normalizer_map s.rho
    ⟨⟨z, hz⟩, Subgroup.mem_normalizer_iff.mpr fun x => ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp hzA x

theorem rho_mem_normalizer_K₂ (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (g : ↥s.G₀)
    (hg : s.rho g ∈ Subgroup.normalizer (((R₂.subgroupOf s.G₀).map s.rho : Subgroup _) : Set _)) :
    s.rho g ∈ Subgroup.normalizer (((K₂.subgroupOf s.G₀).map s.rho : Subgroup _) : Set _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := s.isSylowTwoOf_R₂_sup h135 hR hC h37 h38 h39
  have hle : R₂.map (MulAut.conj (g : G)).toMonoidHom ≤ R₂ ⊔ s.C₀ := by
    rintro _ ⟨r, hr, rfl⟩
    have hrG : r ∈ s.G₀ := s.R₂_le_G₀ hr
    have hgr : (g : G) * r * (g : G)⁻¹ ∈ s.G₀ :=
      s.G₀.mul_mem (s.G₀.mul_mem g.2 hrG) (s.G₀.inv_mem g.2)
    have h1 : s.rho ⟨_, hgr⟩ ∈ (R₂.subgroupOf s.G₀).map s.rho := by
      have e : (⟨_, hgr⟩ : ↥s.G₀) = g * ⟨r, hrG⟩ * g⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hg _).mp ⟨⟨r, hrG⟩, hr, rfl⟩
    obtain ⟨r', hr', hr'e⟩ := h1
    have hk : r'⁻¹ * ⟨_, hgr⟩ ∈ s.rho.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hr'e, inv_mul_cancel]
    have e2 : (g : G) * r * (g : G)⁻¹ = (r' : G) * ((r'⁻¹ * ⟨_, hgr⟩ : ↥s.G₀) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    show (g : G) * r * (g : G)⁻¹ ∈ R₂ ⊔ s.C₀
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr') (Subgroup.mem_sup_right ⟨_, hk, rfl⟩)
  have hcard : Nat.card ↥R₂ ≤ Nat.card ↥(R₂.map (MulAut.conj (g : G)).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective).ge
  have hsyl' := isSylowTwoOf_of_card_le hle (s.isPGroup_R₂.map _) hsyl hcard
  obtain ⟨h, hh, hhe⟩ := hsyl.exists_conj hsyl'
  have hhg : h⁻¹ * (g : G) ∈ Subgroup.normalizer (R₂ : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have e : R₂.map (MulAut.conj (h⁻¹ * (g : G))) =
        (R₂.map (MulAut.conj (g : G)).toMonoidHom).map (MulAut.conj h⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [e, hhe, Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id R₂]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hhgK := (s.N_R₂ hhg).2
  have hRC : R₂ ≤ Subgroup.normalizer (s.C₀ : Set G) := s.R₂_le_G₀.trans s.le_normalizer_C₀
  have hh' : h ∈ (R₂ : Set G) * (s.C₀ : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right R₂ s.C₀ hRC]
    exact hh
  obtain ⟨r, hr, c, hc, rfl⟩ := hh'
  obtain ⟨c', hc', rfl⟩ := hc
  have hrG : r ∈ s.G₀ := s.R₂_le_G₀ hr
  have hhgG : (r * c')⁻¹ * (g : G) ∈ s.G₀ :=
    s.G₀.mul_mem (s.G₀.inv_mem (s.G₀.mul_mem hrG c'.2)) g.2
  have e : g = ⟨r, hrG⟩ * c' * ⟨_, hhgG⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group
  rw [e, map_mul, map_mul, MonoidHom.mem_ker.mp hc', mul_one]
  exact Subgroup.mul_mem _ (s.rho_mem_normalizer_map hrG (s.R₂_le_normalizer_K₂ hr))
    (s.rho_mem_normalizer_map hhgG hhgK)

theorem quasisimple (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    CFSG.IsQuasisimple (ModO2 KZ) :=
  s.KZ_quasisimple h135 hR hC h36 h37 h38 h39
    (cComp_mem_of_le s.KZ_mem s.KZ_cent (Subgroup.centralizer_le_normalizer _)) s.K₂_le_KZ

theorem rho_KZ {k : G} (hk : k ∈ KZ) :
    s.rho ⟨k, s.KZ_le_G₀ hk⟩ = MulAut.conj (QuotientGroup.mk ⟨k, hk⟩ : ModO2 KZ) :=
  L4315.conjModO2_of_mem KZ ⟨k, hk⟩

theorem map_KZ : (KZ.subgroupOf s.G₀).map s.rho =
    (MulAut.conj : ModO2 KZ →* MulAut (ModO2 KZ)).range := by
  ext x
  constructor
  · rintro ⟨⟨k, hkG⟩, hk, rfl⟩
    exact ⟨QuotientGroup.mk ⟨k, hk⟩, (s.rho_KZ hk).symm⟩
  · rintro ⟨q, rfl⟩
    induction q using QuotientGroup.induction_on with
    | H k => exact ⟨⟨k, s.KZ_le_G₀ k.2⟩, k.2, s.rho_KZ k.2⟩

theorem map_K₂_le : (K₂.subgroupOf s.G₀).map s.rho ≤
    (MulAut.conj : ModO2 KZ →* MulAut (ModO2 KZ)).range := by
  rw [← s.map_KZ]
  exact Subgroup.map_mono fun x hx => s.K₂_le_KZ hx

theorem not_K₂_le_pCoreOf_KZ : ¬ K₂ ≤ pCoreOf 2 KZ := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ↥K₂ := (pCoreOf_isPGroup 2 KZ).to_le h
  have : Group.IsSolvable ↥K₂ := by
    have := h2.isNilpotent
    infer_instance
  have hbot := CFSG.LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable s.K₂_perfect
  obtain ⟨k, hk⟩ := s.levi_surjective ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hk1 : (k : G) = 1 := (Subgroup.eq_bot_iff_forall K₂).mp hbot k k.2
  have hk1' : k = 1 := Subtype.ext hk1
  rw [hk1', map_one] at hk
  have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) hk
  simp at this

theorem map_R₂_ne_bot (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    (R₂.subgroupOf s.G₀).map s.rho ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have hq := s.quasisimple h135 hR hC h36 h37 h38 h39
  have hNn : (CFSG.pCore 2 ↥KZ).Normal := CFSG.pCore_normal
  set Inn := (MulAut.conj : ModO2 KZ →* MulAut (ModO2 KZ)).range with hInn
  set Ks := (K₂.subgroupOf s.G₀).map s.rho with hKs
  have hnorm : ∀ k : ↥KZ, MulAut.conj (QuotientGroup.mk k : ModO2 KZ) ∈
      Subgroup.normalizer (Ks : Set (MulAut (ModO2 KZ))) := by
    intro k
    rw [← s.rho_KZ k.2]
    refine s.rho_mem_normalizer_K₂ h135 hR hC h37 h38 h39 _ ?_
    rw [hbot]
    exact Subgroup.mem_normalizer_iff.mpr fun z => by simp
  have hsimple := L4315.isSimpleGroup_inn hq.2.1
  have hKsInn : Ks ≤ Inn := s.map_K₂_le
  have hn : (Ks.subgroupOf Inn).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨_, q, rfl⟩ := g
    induction q using QuotientGroup.induction_on with
    | H k =>
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hnorm k) _).mp hx
  have hrhoK : ∀ k (hk : k ∈ K₂), MulAut.conj (QuotientGroup.mk ⟨k, s.K₂_le_KZ hk⟩ : ModO2 KZ) ∈
      Ks := fun k hk => by
    rw [← s.rho_KZ (s.K₂_le_KZ hk)]
    exact ⟨⟨k, s.K₂_le_G₀ hk⟩, hk, rfl⟩
  have hOK : pCoreOf 2 KZ ≤ Subgroup.normalizer (K₂ : Set G) :=
    s.pCoreOf_KZ_le.trans s.R₂_le_normalizer_K₂
  have hO2solv : Group.IsSolvable ↥(pCoreOf 2 KZ) := by
    have := (pCoreOf_isPGroup 2 KZ).isNilpotent
    infer_instance
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Ks.subgroupOf Inn) with h | h
  ·
    apply s.not_K₂_le_pCoreOf_KZ
    refine L4315.le_pCoreOf_of_central s.K₂_le_KZ s.K₂_perfect fun k hk => ?_
    rw [← L4315.ker_conj, MonoidHom.mem_ker]
    have h1 : (⟨_, hKsInn (hrhoK k hk)⟩ : ↥Inn) ∈ Ks.subgroupOf Inn := hrhoK k hk
    rw [h, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  ·
    have hK₂bar : ∀ k : ↥KZ, ∃ (k₂ : G) (hk₂ : k₂ ∈ K₂),
        (QuotientGroup.mk ⟨k₂, s.K₂_le_KZ hk₂⟩ : ModO2 KZ)⁻¹ *
          QuotientGroup.mk k ∈ Subgroup.center (ModO2 KZ) := by
      intro k
      have h1 : (⟨MulAut.conj (QuotientGroup.mk k : ModO2 KZ), k, rfl⟩ : ↥Inn) ∈
          Ks.subgroupOf Inn := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨⟨k₂, hk₂G⟩, hk₂, he⟩ := (Subgroup.mem_subgroupOf.mp h1 :
        MulAut.conj (QuotientGroup.mk k : ModO2 KZ) ∈ Ks)
      refine ⟨k₂, hk₂, ?_⟩
      rw [← L4315.ker_conj, MonoidHom.mem_ker, map_mul, map_inv]
      have he' : s.rho ⟨k₂, hk₂G⟩ = MulAut.conj (QuotientGroup.mk ⟨k₂, s.K₂_le_KZ hk₂⟩) :=
        s.rho_KZ (s.K₂_le_KZ hk₂)
      rw [← he', he, inv_mul_cancel]
    set K₂b : Subgroup (ModO2 KZ) := (K₂.subgroupOf KZ).map (QuotientGroup.mk' _) with hK₂b
    have hZN : Subgroup.center (ModO2 KZ) ≤ Subgroup.normalizer (K₂b : Set (ModO2 KZ)) :=
      fun z hz => Subgroup.mem_normalizer_iff.mpr fun x => by
        rw [show z * x * z⁻¹ = x by rw [(Subgroup.mem_center_iff.mp hz x).symm,
          mul_inv_cancel_right]]
    have hperfQ : ⁅(⊤ : Subgroup (ModO2 KZ)), (⊤ : Subgroup (ModO2 KZ))⁆ =
        (⊤ : Subgroup (ModO2 KZ)) := by
      rw [← commutator_def]
      exact hq.1.commutator_eq_top
    have hle : (⊤ : Subgroup (ModO2 KZ)) ≤ K₂b ⊔ Subgroup.center (ModO2 KZ) := by
      intro x _
      induction x using QuotientGroup.induction_on with
      | H k =>
        obtain ⟨k₂, hk₂, hz⟩ := hK₂bar k
        have e : (QuotientGroup.mk k : ModO2 KZ) =
            QuotientGroup.mk ⟨k₂, s.K₂_le_KZ hk₂⟩ * ((QuotientGroup.mk ⟨k₂, s.K₂_le_KZ hk₂⟩ :
              ModO2 KZ)⁻¹ * QuotientGroup.mk k) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨⟨k₂, s.K₂_le_KZ hk₂⟩, hk₂, rfl⟩)
          (Subgroup.mem_sup_right hz)
    have htop := L4315.le_of_perfect_of_le_sup hperfQ le_top
      (Group.isSolvable_of_comm fun a b => Subtype.ext
        (Subgroup.mem_center_iff.mp b.2 (a : ModO2 KZ))) hZN hle
    have hKZle : KZ ≤ K₂ ⊔ pCoreOf 2 KZ := by
      intro k hk
      obtain ⟨⟨k₂, hk₂KZ⟩, hk₂, he⟩ := htop (Subgroup.mem_top (QuotientGroup.mk ⟨k, hk⟩))
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at he
      have hq' : k₂⁻¹ * k ∈ pCoreOf 2 KZ := (mem_pCoreOf_iff' _).mpr he
      have e : k = k₂ * (k₂⁻¹ * k) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk₂) (Subgroup.mem_sup_right hq')
    have hKZperf : ⁅KZ, KZ⁆ = KZ := perfect_of_mem_cComp s.KZ_mem
    have hKZK₂ := L4315.le_of_perfect_of_le_sup hKZperf s.K₂_le_KZ hO2solv hOK hKZle
    exact (s.lemma_4_3_13 h135 hR hC h37 h38 h39 s.KZ_normal s.K₂_le_KZ).ne
      (le_antisymm s.K₂_le_KZ hKZK₂)

end Setting4315

theorem Setting4311.setting4315 {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ}
    {F : Type} [Field F] [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)}
    {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)} {W' : Submodule F (Fin 3 → F)}
    {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
    (s : Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y) (h314 : Step4314)
    (hKZ : KZ ∈ cComp (Subgroup.normalizer (ZS : Set G)))
    (hGZ : Subgroup.normalizer (ZS : Set G) ≤ Subgroup.normalizer (KZ : Set G)) (hK₂ : K₂ ≤ KZ)
    (hKZC : KZ ≤ Subgroup.centralizer (ZS : Set G)) :
    Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ := by
  obtain ⟨h1, -, h3, h4⟩ := h314 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ s hKZ hGZ hK₂ hKZC
  exact ⟨s, hKZ, hGZ, hK₂, hKZC, h1, h3, h4⟩

end CFSG.Quasithin.H13.Ch4
