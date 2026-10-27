module

public import CFSG.Foundations.Basic
public import CFSG.RankThree.S4Free.StellmacherHosts
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.LieType.Ree.SuzukiOrder
import CFSG.LocalAnalysis.SectionRank.SuzukiCover
import CFSG.Quasithin.Background.G8Core
import CFSG.Quasithin.Background.KnownMultOdd
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG

private theorem res1340_mul_comm_of_ne {S : Type*} [Group S] [Finite S] {A B : Subgroup S}
    (hA : IsComponent A) (hB : IsComponent B) (hne : A ≠ B) :
    ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := by
  rcases CFSG.LocalCores.distinct_components_commute hA hB with h | h
  · exact absurd h hne
  · intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx) y hy).symm

private theorem res1340_inf_eq_bot_of_center_eq_bot {S : Type*} [Group S] {A B : Subgroup S}
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hA : Subgroup.center ↥A = ⊥) : A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxA, hxB⟩
  have hx : (⟨x, hxA⟩ : ↥A) ∈ Subgroup.center ↥A :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hAB g g.2 x hxB)
  rw [hA, Subgroup.mem_bot] at hx
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx)

theorem res1340_center_eq_bot_of_isComponent {S : Type} [Group S] [Finite S]
    (hS2 : CFSG.pCore 2 S = ⊥) (hSz : CFSG.RankThree.S4Free.SzSections S) {J : Subgroup S}
    (hJ : CFSG.IsComponent J) : Subgroup.center ↥J = ⊥ := by
  have : Group.IsPerfect ↥J := hJ.1.1
  obtain ⟨a, ha, K, _, _, hK, ⟨e⟩⟩ := hSz J (Subgroup.center ↥J) hJ.1.2.1 hJ.1.2.2
  have hmodel : CFSG.Blueprint.SuzukiModel (↥J ⧸ Subgroup.center ↥J) 2 (2 * a + 1) :=
    ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨e⟩⟩
  obtain ⟨b, hb, ⟨e'⟩⟩ :=
    CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hmodel
  have h2 : IsPGroup 2 (Subgroup.center ↥J) :=
    CFSG.Quasithin.isPGroup_two_of_mulEquiv_cyclic_odd_sylow (Subgroup.center ↥J) le_rfl e'
      fun _ _ hr2 _ Q => CFSG.SectionRank.suzuki_sylow_isCyclic b hb hr2 Q
  have hle : (Subgroup.center ↥J).map J.subtype ≤ CFSG.pCore 2 S :=
    CFSG.Quasithin.G8.le_pCore_of_le_fitting
      ((CFSG.LocalCores.center_component_le_center_layer hJ).trans
        CFSG.WholeGroup.center_layer_le_fittingSubgroup) (h2.map J.subtype)
  rw [hS2, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp hle

theorem res1340_five_dvd_card_of_isComponent {S : Type}
    [Group S] [Finite S] (hSz : CFSG.RankThree.S4Free.SzSections S) {J : Subgroup S}
    (hJ : CFSG.IsComponent J) : 5 ∣ Nat.card J := by
  obtain ⟨a, -, K, _, _, hK, ⟨e⟩⟩ := hSz J (Subgroup.center ↥J) hJ.1.2.1 hJ.1.2.2
  have h5 : 5 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
    exact (CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.five_dvd_sq_add_one
      (CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.two_pow_mod_five
        (odd_two_mul_add_one a))).mul_left _
  exact h5.trans (Subgroup.card_quotient_dvd_card _)

theorem res1340_eq_or_eq_of_pRank_five {S : Type} [Group S] [Finite S]
    (h5 : CFSG.Open.pRank 5 (⊤ : Subgroup S) ≤ 2)
    (hZ : ∀ J : Subgroup S, CFSG.IsComponent J → Subgroup.center ↥J = ⊥)
    (h5J : ∀ J : Subgroup S, CFSG.IsComponent J → 5 ∣ Nat.card J) {J₁ J₂ J₃ : Subgroup S}
    (h1 : CFSG.IsComponent J₁) (h2 : CFSG.IsComponent J₂) (h3 : CFSG.IsComponent J₃) :
    J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h12, h13, h23⟩ := hcon
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hex : ∀ J : Subgroup S, IsComponent J → ∃ x : S, x ∈ J ∧ orderOf x = 5 := by
    intro J hJ
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 5 (h5J J hJ)
    exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩
  obtain ⟨x₁, hx₁J, hx₁⟩ := hex J₁ h1
  obtain ⟨x₂, hx₂J, hx₂⟩ := hex J₂ h2
  obtain ⟨x₃, hx₃J, hx₃⟩ := hex J₃ h3
  have c12 := res1340_mul_comm_of_ne h1 h2 h12
  have c13 := res1340_mul_comm_of_ne h1 h3 h13
  have c23 := res1340_mul_comm_of_ne h2 h3 h23
  have c1_23 : ∀ x ∈ J₁, ∀ y ∈ J₂ ⊔ J₃, x * y = y * x := by
    intro x hx y hy
    have hle : J₂ ⊔ J₃ ≤ Subgroup.centralizer ({x} : Set S) :=
      sup_le (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr (c12 x hx z hz).symm)
        (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr (c13 x hx z hz).symm)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm
  have hinf1 : J₁ ⊓ (J₂ ⊔ J₃) = ⊥ := res1340_inf_eq_bot_of_center_eq_bot c1_23 (hZ J₁ h1)
  have hinf2 : J₂ ⊓ J₃ = ⊥ := res1340_inf_eq_bot_of_center_eq_bot c23 (hZ J₂ h2)
  have hpow : ∀ {x : S}, orderOf x = 5 → x ^ 5 = 1 := fun {x} hx => by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hE₁ := CFSG.Open.isElemAbelian_zpowers (hpow hx₁)
  have hE₂ := CFSG.Open.isElemAbelian_zpowers (hpow hx₂)
  have hE₃ := CFSG.Open.isElemAbelian_zpowers (hpow hx₃)
  have hE₁J : Subgroup.zpowers x₁ ≤ J₁ := Subgroup.zpowers_le.mpr hx₁J
  have hE₂J : Subgroup.zpowers x₂ ≤ J₂ := Subgroup.zpowers_le.mpr hx₂J
  have hE₃J : Subgroup.zpowers x₃ ≤ J₃ := Subgroup.zpowers_le.mpr hx₃J
  let f₂₃ : ↥(Subgroup.zpowers x₂) × ↥(Subgroup.zpowers x₃) →* S :=
    MonoidHom.noncommCoprod (Subgroup.zpowers x₂).subtype (Subgroup.zpowers x₃).subtype
      fun a b => c23 a (hE₂J a.2) b (hE₃J b.2)
  let f : ↥(Subgroup.zpowers x₁) × ↥(Subgroup.zpowers x₂) × ↥(Subgroup.zpowers x₃) →* S :=
    MonoidHom.noncommCoprod (Subgroup.zpowers x₁).subtype f₂₃
      fun a bc => Commute.mul_right (c12 a (hE₁J a.2) bc.1 (hE₂J bc.1.2))
        (c13 a (hE₁J a.2) bc.2 (hE₃J bc.2.2))
  have hf_apply : ∀ (a : ↥(Subgroup.zpowers x₁)) (b : ↥(Subgroup.zpowers x₂))
      (c : ↥(Subgroup.zpowers x₃)), f (a, b, c) = (a : S) * ((b : S) * (c : S)) :=
    fun _ _ _ => rfl
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b, c⟩ habc
    have h : (a : S) * ((b : S) * (c : S)) = 1 :=
      (hf_apply a b c).symm.trans (MonoidHom.mem_ker.mp habc)
    have ha1 : (a : S) = 1 := by
      have hmem : (a : S) ∈ J₁ ⊓ (J₂ ⊔ J₃) :=
        ⟨hE₁J a.2, by
          rw [eq_inv_of_mul_eq_one_left h]
          exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (hE₂J b.2))
            (Subgroup.mem_sup_right (hE₃J c.2)))⟩
      rwa [hinf1, Subgroup.mem_bot] at hmem
    rw [ha1, one_mul] at h
    have hb1 : (b : S) = 1 := by
      have hmem : (b : S) ∈ J₂ ⊓ J₃ :=
        ⟨hE₂J b.2, by
          rw [eq_inv_of_mul_eq_one_left h]
          exact Subgroup.inv_mem _ (hE₃J c.2)⟩
      rwa [hinf2, Subgroup.mem_bot] at hmem
    rw [hb1, one_mul] at h
    exact Subgroup.mem_bot.mpr
      (Prod.ext (Subtype.ext ha1) (Prod.ext (Subtype.ext hb1) (Subtype.ext h)))
  have h3le : 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup S) :=
    CFSG.SectionRank.le_pRank_of_injective (p := 5) (by norm_num)
      (A := ↥(Subgroup.zpowers x₁) × ↥(Subgroup.zpowers x₂) × ↥(Subgroup.zpowers x₃))
      (fun ⟨a, b, c⟩ ⟨a', b', c'⟩ =>
        Prod.ext (mul_comm' a a') (Prod.ext (mul_comm' b b') (mul_comm' c c')))
      (fun ⟨a, b, c⟩ => Prod.ext (Subtype.ext (hE₁.2 _ a.2))
        (Prod.ext (Subtype.ext (hE₂.2 _ b.2)) (Subtype.ext (hE₃.2 _ c.2))))
      (k := 3)
      (by rw [Nat.card_prod, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, Nat.card_zpowers,
        hx₁, hx₂, hx₃]; norm_num)
      f hinj le_top
  omega

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
