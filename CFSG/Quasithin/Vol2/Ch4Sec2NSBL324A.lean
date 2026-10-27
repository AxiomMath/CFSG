module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBDefs
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Typ
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k : ℕ}

private theorem mem_pCoreOf_iff_nsb324a {L : Subgroup G} (a : ↥L) :
    (a : G) ∈ pCoreOf 2 L ↔ a ∈ CFSG.pCore 2 ↥L := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = a := Subtype.ext hyx
    subst this
    exact hy
  · intro ha
    exact ⟨a, ha, rfl⟩

private theorem mk_eq_iff_nsb324a {L : Subgroup G} (a b : ↥L) :
    (QuotientGroup.mk a : ModO2 L) = QuotientGroup.mk b ↔
      ((a⁻¹ * b : ↥L) : G) ∈ pCoreOf 2 L := by
  rw [QuotientGroup.eq, mem_pCoreOf_iff_nsb324a]

private theorem conj_mem_pCoreOf_nsb324a {L : Subgroup G} {l : G} (hl : l ∈ L) {c : G}
    (hc : c ∈ pCoreOf 2 L) : l * c * l⁻¹ ∈ pCoreOf 2 L :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl) c).mp hc

private theorem pCore_map_eq_nsb324a {L : Subgroup G} (e : ↥L ≃* ↥L) :
    (CFSG.pCore 2 ↥L).map e.toMonoidHom = CFSG.pCore 2 ↥L := by
  have hle : ∀ f : ↥L ≃* ↥L, (CFSG.pCore 2 ↥L).map f.toMonoidHom ≤ CFSG.pCore 2 ↥L := by
    intro f
    have hp : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
    exact le_sSup ⟨CFSG.pCore_normal.map f.toMonoidHom f.surjective, hp.map f.toMonoidHom⟩
  refine le_antisymm (hle e) ?_
  intro x hx
  refine Subgroup.mem_map.mpr ⟨e.symm x, hle e.symm (Subgroup.mem_map_of_mem e.symm.toMonoidHom hx),
    ?_⟩
  simp

private def conjLAut_nsb324a {L : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) : ↥L ≃* ↥L where
  toFun z := ⟨y * z * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy z).mp z.2⟩
  invFun z := ⟨y⁻¹ * z * y⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) z).mp z.2⟩
  left_inv z := Subtype.ext (by simp [mul_assoc])
  right_inv z := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

private theorem conjLAut_coe_nsb324a {L : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) (z : ↥L) :
    ((conjLAut_nsb324a hy z : ↥L) : G) = y * z * y⁻¹ :=
  rfl

private noncomputable def conjModO2_nsb324a {L : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) : ModO2 L ≃* ModO2 L :=
  QuotientGroup.congr (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥L) (conjLAut_nsb324a hy)
    (pCore_map_eq_nsb324a _)

private theorem conjModO2_mul_nsb324a {L : Subgroup G} {y y' : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) (hy' : y' ∈ Subgroup.normalizer (L : Set G)) :
    conjModO2_nsb324a (Subgroup.mul_mem _ hy hy') =
      conjModO2_nsb324a hy * conjModO2_nsb324a hy' := by
  apply MulEquiv.ext
  intro q
  refine QuotientGroup.induction_on q fun z => ?_
  show QuotientGroup.mk (conjLAut_nsb324a (Subgroup.mul_mem _ hy hy') z) =
    QuotientGroup.mk (conjLAut_nsb324a hy (conjLAut_nsb324a hy' z))
  congr 1
  apply Subtype.ext
  simp [conjLAut_coe_nsb324a, mul_assoc]

private noncomputable def actModO2_nsb324a {M L : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) : ↥M →* MulAut (ModO2 L) :=
  MonoidHom.mk' (fun y => conjModO2_nsb324a (hMN y.2))
    (fun a b => conjModO2_mul_nsb324a (hMN a.2) (hMN b.2))

private theorem actModO2_mem_inner_nsb324a {M L : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) {l : G} (hl : l ∈ L) (hlM : l ∈ M) :
    actModO2_nsb324a hMN ⟨l, hlM⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (ModO2 L) := by
  refine MonoidHom.mem_range.mpr ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨l, hl⟩, ?_⟩
  apply MulEquiv.ext
  intro q
  refine QuotientGroup.induction_on q fun z => ?_
  rfl

private noncomputable def thetaNsb324a {M L : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) :
    ↥M →* CFSG.ComponentClassification.OuterAutomorphisms.Outer (ModO2 L) :=
  (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (ModO2 L))).comp
    (actModO2_nsb324a hMN)

private theorem theta_eq_one_iff_nsb324a {M L : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) (y : ↥M) :
    thetaNsb324a hMN y = 1 ↔
      actModO2_nsb324a hMN y ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (ModO2 L) :=
  QuotientGroup.eq_one_iff _

private theorem actModO2_eq_one_nsb324a {M L : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) (m : ↥M)
    (hm : (m : G) ∈ centralizerSection M L (pCoreOf 2 L)) :
    actModO2_nsb324a hMN m = 1 := by
  obtain ⟨-, -, -, hcomm⟩ := mem_centralizerSection.mp hm
  apply MulEquiv.ext
  intro q
  refine QuotientGroup.induction_on q fun z => ?_
  show QuotientGroup.mk (conjLAut_nsb324a (hMN m.2) z) = QuotientGroup.mk z
  refine ((mk_eq_iff_nsb324a z (conjLAut_nsb324a (hMN m.2) z)).mpr ?_).symm
  have h := hcomm (z : G)⁻¹ (L.inv_mem z.2)
  convert h using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjLAut_coe_nsb324a]
  group

private theorem exists_centralizer_of_inner_nsb324a {M L : Subgroup G} (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) (y : ↥M)
    (hin : actModO2_nsb324a hMN y ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (ModO2 L)) :
    ∃ l ∈ L, l⁻¹ * (y : G) ∈ centralizerSection M L (pCoreOf 2 L) := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hin
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) x
  have hz : ∀ z : ↥L,
      ((((l * z * l⁻¹)⁻¹ * conjLAut_nsb324a (hMN y.2) z : ↥L)) : G) ∈ pCoreOf 2 L := by
    intro z
    have h := congrArg (fun f : MulAut (ModO2 L) => f (QuotientGroup.mk z)) hx
    have h' : (QuotientGroup.mk (l * z * l⁻¹) : ModO2 L) =
        QuotientGroup.mk (conjLAut_nsb324a (hMN y.2) z) := h
    exact (mk_eq_iff_nsb324a _ _).mp h'
  refine ⟨(l : G), l.2, ?_⟩
  refine mem_centralizerSection.mpr ⟨M.mul_mem (M.inv_mem (hLM l.2)) y.2, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer l.2)) (hMN y.2)
  · exact Subgroup.mul_mem _
      (Subgroup.inv_mem _ (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
        (Subgroup.le_normalizer l.2)))
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hMN y.2))
  · intro x hx
    obtain ⟨z, hzx⟩ : ∃ z : ↥L, (z : G) = x⁻¹ := ⟨⟨x⁻¹, L.inv_mem hx⟩, rfl⟩
    have hc := conj_mem_pCoreOf_nsb324a (L.inv_mem l.2) (hz z)
    have e : x * ((l : G)⁻¹ * (y : G)) * x⁻¹ * ((l : G)⁻¹ * (y : G))⁻¹ =
        (l : G)⁻¹ * ((((l * z * l⁻¹)⁻¹ * conjLAut_nsb324a (hMN y.2) z : ↥L)) : G) *
          ((l : G)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjLAut_coe_nsb324a, hzx]
      group
    rw [e]
    exact hc

private theorem card_outer_modO2_dvd_two_nsb324a (hd : NoSumBigData G T M L Mm I H K m k) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (ModO2 L)) ∣ 2 := by
  obtain ⟨e⟩ := hd.2.2.1.nonempty_modO2_equiv
  have hm3 : 3 ≤ m := by
    rcases hd.2.2.2.1 with h | h <;> omega
  have hb := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound
    (ModO2 (perfectCore (L ⊓ H))) m 2 1 hd.2.2.2.2.2.2.1).2.2.2.2 hm3
  have hcard : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (ModO2 (perfectCore (L ⊓ H)))) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (ModO2 L)) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
  rw [← hcard]
  simpa using hb

theorem M_le_L_sup_C_aux (hd : NoSumBigData G T M L Mm I H K m k)
    (hT : ∀ t ∈ T, ∃ l ∈ L, l⁻¹ * t ∈ centralizerSection M L (pCoreOf 2 L)) :
    ∀ y ∈ M, ∃ l ∈ L, l⁻¹ * y ∈ centralizerSection M L (pCoreOf 2 L) := by
  intro y hy
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  have hLM : L ≤ M := hc.hyp421.L_le
  have hTM : T ≤ M := hc.hyp421.T_le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hc.normal
  have hodd : ¬ 2 ∣ (T.subgroupOf M).index :=
    (CFSG.Quasithin.H13.Ch4.isSylowTwoOf_of_le hc.hyp421.sylow hTM).2.2
  have hOut := card_outer_modO2_dvd_two_nsb324a hd
  have hTK : T.subgroupOf M ≤ (thetaNsb324a hMN).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, theta_eq_one_iff_nsb324a]
    obtain ⟨l, hlL, hlC⟩ := hT (x : G) (Subgroup.mem_subgroupOf.mp hx)
    have hlM : l⁻¹ * (x : G) ∈ M := (mem_centralizerSection.mp hlC).1
    have hfac : x = (⟨l, hLM hlL⟩ : ↥M) * ⟨l⁻¹ * (x : G), hlM⟩ :=
      Subtype.ext (by simp)
    have h1 : actModO2_nsb324a hMN ⟨l⁻¹ * (x : G), hlM⟩ = 1 :=
      actModO2_eq_one_nsb324a hMN _ hlC
    rw [hfac, map_mul, h1, mul_one]
    exact actModO2_mem_inner_nsb324a hMN hlL (hLM hlL)
  have hidx : (thetaNsb324a hMN).ker.index ∣ 2 := by
    rw [Subgroup.index_ker]
    exact (Subgroup.card_subgroup_dvd_card _).trans hOut
  have hK1 : (thetaNsb324a hMN).ker.index = 1 := by
    have hdvd : (thetaNsb324a hMN).ker.index ∣ (T.subgroupOf M).index :=
      Subgroup.index_dvd_of_le hTK
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h | h
    · exact h
    · exfalso
      rw [h] at hdvd
      exact hodd hdvd
  have htop : (thetaNsb324a hMN).ker = ⊤ := Subgroup.index_eq_one.mp hK1
  have hyK : (⟨y, hy⟩ : ↥M) ∈ (thetaNsb324a hMN).ker := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [MonoidHom.mem_ker, theta_eq_one_iff_nsb324a] at hyK
  exact exists_centralizer_of_inner_nsb324a hLM hMN ⟨y, hy⟩ hyK

end CFSG.Quasithin.H13.Ch4.NSB
