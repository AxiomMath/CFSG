module

public import CFSG.RankThree.PartOne.K133Spor.HN
public import CFSG.RankThree.PartOne.K133Spor.HNClassA
public import Certificates.Certificate14998
public import CFSG.Sporadic.HNOddCore.Fusion
public import CFSG.Sporadic.HNOddCore.FusB
public import CFSG.Sporadic.HNOddCore.ThreeInvol
public import CFSG.Sporadic.HNSchreier.Faithful
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.RankThree.PartOne.S12.Sec137
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer
public import CFSG.Walter.ReeOrder.JT.Section7B
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate2
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.RankThree.PartOne.K133Spor Subgroup

@[expose] def HNClass {G : Type*} [Group G] (a : G) : Prop :=
  ∀ D : Subgroup G, (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) → (∀ d ∈ D, d ^ 5 = 1) →
    Nat.card D = 25 → (∀ d ∈ D, d * a = a * d) → ∀ t' : G, t' * a = a * t' → t' ^ 2 = 1 →
      t' ≠ 1 → t' ≠ a → (∀ d ∈ D, d * t' = t' * d) → False

theorem hnClass_conj {G : Type*} [Group G] [Finite G] {a : G} (h : HNClass a) (D V : Subgroup G)
    (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hD5 : ∀ d ∈ D, d ^ 5 = 1) (hDc : Nat.card D = 25)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hVc : Nat.card V = 4)
    (hDV : ∀ d ∈ D, ∀ v ∈ V, d * v = v * d) {t : G} (htV : t ∈ V) (ht1 : t ≠ 1) {g : G}
    (hg : g * t * g⁻¹ = a) : False := by
  classical
  have hzp : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hV2 t htV) ht1
  obtain ⟨t', ht'V, ht'z⟩ : ∃ t' ∈ V, t' ∉ zpowers t := by
    by_contra hcon
    push Not at hcon
    have hle : V ≤ zpowers t := hcon
    have := Subgroup.card_le_of_le hle
    rw [hzp, hVc] at this
    omega
  have ht'1 : t' ≠ 1 := fun h => ht'z (h ▸ one_mem _)
  have ht't : t' ≠ t := fun h => ht'z (h ▸ mem_zpowers _)
  let φ : MulAut G := MulAut.conj g
  have hφ : ∀ y, φ y = g * y * g⁻¹ := fun y => MulAut.conj_apply g y
  refine h (D.map φ.toMonoidHom) ?_ ?_ ?_ ?_ (φ t') ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show φ x * φ y = φ y * φ x
    rw [← map_mul, ← map_mul, hDab x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    show φ x ^ 5 = 1
    rw [← map_pow, hD5 x hx, map_one]
  · rw [Subgroup.card_map_of_injective φ.injective, hDc]
  · rintro _ ⟨x, hx, rfl⟩
    show φ x * a = a * φ x
    rw [← hg, ← hφ t, ← map_mul, ← map_mul, hDV x hx t htV]
  · show φ t' * a = a * φ t'
    rw [← hg, ← hφ t, ← map_mul, ← map_mul, hVab t' ht'V t htV]
  · rw [← map_pow, hV2 t' ht'V, map_one]
  · intro h1
    exact ht'1 (φ.injective (by rw [h1, map_one]))
  · intro h1
    apply ht't
    apply φ.injective
    rw [h1, ← hg]
    exact (hφ t).symm
  · rintro _ ⟨x, hx, rfl⟩
    show φ x * φ t' = φ t' * φ x
    rw [← map_mul, ← map_mul, hDV x hx t' ht'V]


theorem hnClass_aJ
    : HNClass aJ := by
  intro D hDab hD5 hDc hDa t' ht'a ht'2 ht'1 ht'ne hDt'
  exact K133Spor.hnClassA D hDab hD5 hDc
    (fun d hd => Subgroup.mem_centralizer_singleton_iff.2 (hDa d hd))
    (Subgroup.mem_centralizer_singleton_iff.2 ht'a) ht'2 ht'1 ht'ne hDt'
    Certificates.certificate14998

theorem hnCore
    (hA : HNClass aJ) (hB : HNClass t4J) (D V : Subgroup JH)
    (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hD5 : ∀ d ∈ D, d ^ 5 = 1) (hDc : Nat.card D = 25)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hVc : Nat.card V = 4)
    (hDV : ∀ d ∈ D, ∀ v ∈ V, d * v = v * d) : False := by
  classical
  obtain ⟨t, htV, ht1⟩ : ∃ t ∈ V, t ≠ 1 := by
    by_contra h
    push Not at h
    have : V = ⊥ := (Subgroup.eq_bot_iff_forall V).mpr h
    rw [this, Subgroup.card_bot] at hVc
    omega
  have ht2 : t ^ 2 = 1 := hV2 t htV
  obtain ⟨hcover, -, -, -, hJ, -⟩ := ctuc_hn_involution_fusion_and_local_stabilizers
  have hy2 : (jR t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hy1 : jR t ≠ 1 := fun h => ht1 (jR_injective (by rw [h, map_one]))
  rcases hcover (jR t) hy2 hy1 with h | h | h
  · exact not_isConj_c_jR t h
  · have hx2 : (jR t2J) ^ 2 = 1 := by rw [← map_pow, t2J_sq, map_one]
    have hx1 : jR t2J ≠ 1 := fun h' => t2J_ne_one (jR_injective (by rw [h', map_one]))
    obtain ⟨g, hg⟩ := hJ (jR t2J) (jR t) hx2 hx1 h
    have hg' : g * t2J * g⁻¹ = t := jR_injective (by rw [← hg]; simp [map_mul, map_inv])
    obtain ⟨c, hc⟩ := isConj_iff.1 isConj_t2_aJ
    refine hnClass_conj hA D V hDab hD5 hDc hVab hV2 hVc hDV htV ht1 (g := c * g⁻¹) ?_
    rw [← hg']
    calc c * g⁻¹ * (g * t2J * g⁻¹) * (c * g⁻¹)⁻¹ = c * t2J * c⁻¹ := by group
      _ = aJ := hc
  · have hx2 : (jR t4J) ^ 2 = 1 := by rw [← map_pow, sq, t4J_sq, map_one]
    have hx1 : jR t4J ≠ 1 := fun h' => t4J_ne_one (jR_injective (by rw [h', map_one]))
    obtain ⟨g, hg⟩ := hJ (jR t4J) (jR t) hx2 hx1 h
    have hg' : g * t4J * g⁻¹ = t := jR_injective (by rw [← hg]; simp [map_mul, map_inv])
    refine hnClass_conj hB D V hDab hD5 hDc hVab hV2 hVc hDV htV ht1 (g := g⁻¹) ?_
    rw [← hg']
    group


theorem transport_klein {T G : Type*} [Group T] [Group G] (eJ : T ≃* G) (D V : Subgroup T)
    (hD : IsElementaryAbelian 5 D) (hDc : Nat.card D = 25) (hV : IsElementaryAbelian 2 V)
    (hVc : Nat.card V = 4) (hDV : ∀ d ∈ D, ∀ v ∈ V, d * v = v * d)
    (hcore : ∀ D' V' : Subgroup G, (∀ x ∈ D', ∀ y ∈ D', x * y = y * x) → (∀ d ∈ D', d ^ 5 = 1) →
      Nat.card D' = 25 → (∀ x ∈ V', ∀ y ∈ V', x * y = y * x) → (∀ v ∈ V', v ^ 2 = 1) →
      Nat.card V' = 4 → (∀ d ∈ D', ∀ v ∈ V', d * v = v * d) → False) : False := by
  have := hD
  have := hV
  refine hcore (D.map eJ.toMonoidHom) (V.map eJ.toMonoidHom) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show eJ x * eJ y = eJ y * eJ x
    rw [← map_mul, ← map_mul]
    exact congrArg eJ (congrArg Subtype.val (hD.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · rintro _ ⟨x, hx, rfl⟩
    show eJ x ^ 5 = 1
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian x hx, map_one]
  · rw [Subgroup.card_map_of_injective eJ.injective, hDc]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show eJ x * eJ y = eJ y * eJ x
    rw [← map_mul, ← map_mul]
    exact congrArg eJ (congrArg Subtype.val (hV.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · rintro _ ⟨x, hx, rfl⟩
    show eJ x ^ 2 = 1
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian x hx, map_one]
  · rw [Subgroup.card_map_of_injective eJ.injective, hVc]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show eJ x * eJ y = eJ y * eJ x
    rw [← map_mul, ← map_mul, hDV x hx y hy]

theorem hnKleinPlaneFree_of_classes
    (hA : HNClass aJ) (hB : HNClass t4J) : HNKleinPlaneFree := by
  intro T _ _ ⟨e⟩ D V hD hDc hV hVc hDV
  let eJ : T ≃* JH := e.trans hnEquivJ
  exact @transport_klein T JH _ inferInstance eJ D V hD hDc hV hVc hDV fun D' V' h1 h2 h3 h4 h5 h6 h7 =>
    hnCore hA hB D' V' h1 h2 h3 h4 h5 h6 h7


theorem hnKleinPlaneFree_of_classB
    (hB : HNClass t4J) : HNKleinPlaneFree :=
  hnKleinPlaneFree_of_classes hnClass_aJ hB

end CFSG.RankThree.PartOne.K133
