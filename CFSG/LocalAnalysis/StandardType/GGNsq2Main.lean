module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSQ2CellsDefs
public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import Certificates.Certificate10015
public import Certificates.Certificate10016
public import Certificates.Certificate10017
public import Certificates.Certificate10018
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotActs
import CFSG.LocalAnalysis.StandardType.GGNsq2Hopf
import CFSG.LocalAnalysis.StandardType.GGNsq2RankOne
import CFSG.LocalAnalysis.StandardType.GGNsq2Block
import CFSG.LocalAnalysis.StandardType.GGNsq2Rank
import CFSG.LocalAnalysis.StandardType.GGNsq2DetInv
import CFSG.LocalAnalysis.StandardType.GGNsq2Strict
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosFinal
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapterAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSCornerMain
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.CoprimeKernel CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LieType.Steinberg

open scoped MatrixGroups

namespace NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]
variable {p : ℕ} {N : Subgroup G} {f : ↥N →* Q} {L Bs Z : Subgroup G}

theorem Datum.f_mem_normalizer_img (hD : Datum p N f L Bs Z)
    (hBsL : Bs ≤ Subgroup.normalizer (L : Set G)) {b : G} (hb : b ∈ Bs) :
    f ⟨b, hD.BsN hb⟩ ∈ Subgroup.normalizer ((img N f L : Subgroup Q) : Set Q) := by
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hBsL hb
  have hbinv : ∀ h ∈ L, b⁻¹ * h * b ∈ L := fun h hh => by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hbN) h).1 hh
    simpa using this
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨l, hl, rfl⟩ := mem_img.1 hy
    refine mem_img.2 ⟨⟨b, hD.BsN hb⟩ * l * ⟨b, hD.BsN hb⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.1 hbN _).1 hl
  · intro hy
    obtain ⟨l', hl', hl'f⟩ := mem_img.1 hy
    refine mem_img.2 ⟨⟨b, hD.BsN hb⟩⁻¹ * l' * ⟨b, hD.BsN hb⟩, hbinv _ hl', ?_⟩
    rw [map_mul, map_mul, map_inv, hl'f]
    group

end NsQuot

open NsQuot

theorem ggNsq2Member_exists_rankOne_of_or
    (hU : GGU62OuterDiagInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hcentX : Nat.card ↥(B ⊓ Subgroup.centralizer (X : Set G)) = p)
    (hcentBsX : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ 3)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hdvd : p ∣ 2 ^ 1 + 1)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥X = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hbs : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (h3pow : 720 ≤ Nat.card ↥(ggAutomizer X Bs) →
      3 ^ 6 ≤ Nat.card ↥Bs ∨ Subgroup.center ↥X = ⊥) :
    ∃ r ∈ ggAutomizer X Bs, GGIsReflection p r ∧ Nat.card ↥(ggRankOneIn X Bs r) = 6 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  have hp3 : p = 3 := by
    have h3 : p ∣ 3 := by simpa using hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
  subst hp3
  have hBsExp : ∀ b ∈ Bs, b ^ 3 = 1 := hconf.2.1.2.1.2
  obtain ⟨Q, _, _, f, hD⟩ := exists_quotient_datum hp hodd hBsN hBsExp
  have hperfL : Group.IsPerfect ↥X := ⟨hperf⟩
  obtain ⟨η, hη⟩ := hD.exists_eta θ
  have hmax : ∀ l : ↥X, l ∈ Subgroup.center ↥X → (∃ k : ℕ, l ^ (2 ^ k) = 1) →
      (l : G) ∈ twoCentral X := fun l hc hk => mem_twoCentral_of_center hc hk
  have hηsurj := hD.eta_surjective hη
  have hηker := hD.eta_ker_le_center hη
  have hηcop := hD.eta_ker_coprime_four hη hmax
  have : Group.IsPerfect ↥(img _ f X) := Group.IsPerfect.ofSurjective hD.fL_surjective
  obtain ⟨ψ, hψsurj, hψη⟩ := exists_cover_u62 hK η hηsurj inferInstance hηker hηcop
  let ee : Su K 2 1 6 ≃* ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    MulEquiv.subgroupCongr (su_eq_largeEven hK)
  let ψ₀ : Su K 2 1 6 →* ↥(img _ f X) := ψ.comp ee.toMonoidHom
  have hψ₀surj : Function.Surjective ψ₀ := hψsurj.comp ee.surjective
  have hψ₀η : ∀ s, η (ψ₀ s) = LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
      (MulEquiv.subgroupCongr (su_eq_largeEven hK) s) := fun s => hψη (ee s)
  have hψ₀ker : ψ₀.ker ≤ Subgroup.center (Su K 2 1 6) := by
    intro s hs
    have h1 : η (ψ₀ s) = 1 := by rw [MonoidHom.mem_ker.1 hs, map_one]
    rw [hψ₀η s] at h1
    have hz : (ee s) ∈ (LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
      (QuotientGroup.eq_one_iff _).1 h1
    have hz' : ((ee s : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) ∈
        Subgroup.center (GL (Fin 6) K) := by
      have h3 := Subgroup.mem_subgroupOf.1 hz
      rwa [largeEvenScalars_def, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h3
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hz' (y : GL (Fin 6) K)
  have hacts : GGActsUnitarily (p := 2) (f := 1) ((img _ f X).subtype.comp ψ₀) (img _ f Bs) := by
    intro bq hbq
    obtain ⟨bn, hbnB, rfl⟩ := mem_img.1 hbq
    obtain ⟨φ, hφI, hInd⟩ := hbs (bn : G) hbnB
    have hnorm := hD.f_mem_normalizer_img hBsN hbnB
    have hbY : ∀ y ∈ img _ f X, f bn * y * (f bn)⁻¹ ∈ img _ f X := fun y hy =>
      (Subgroup.mem_normalizer_iff.1 hnorm y).1 hy
    exact ggNSq2_acts_quot hK (by norm_num) η hηker ψ₀ hψ₀η hbY hφI (hD.eta_induces hη hBsN hbnB hInd)
  have hlocal := NsQuot.ggNSLocalHyp_of_quot hcfg hD hperfL hcentX hK (by norm_num)
    (by norm_num) hdvd hψ₀ker hψ₀surj hacts
  obtain ⟨c, hc⟩ := ggNSLocal_exists_diag ggSecFiveNSCornerInput_holds hlocal
  have h' := hlocal.comp_conj c
  have hrange : (((img _ f X).subtype.comp ψ₀).comp (MulAut.conj c).toMonoidHom).range = img _ f X := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective, Subgroup.map_top,
      MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ₀surj, Subgroup.map_top,
      Subgroup.range_subtype]
  have hpos := ggNSDiag_position h' hc
  rw [hrange] at hpos
  unfold GGTableBPosSU at hpos
  obtain ⟨ε, hεrefl, hεblock⟩ := hpos
  have h720 : Nat.card ↥(ggAutomizer (img _ f X) (img _ f Bs)) = 720 := by
    have h6 : (6 : ℕ).factorial = 720 := by decide
    rw [← Nat.card_congr ε.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin, h6]
  have hAL : 720 ≤ Nat.card ↥(ggAutomizer X Bs) := by
    rw [← h720]
    exact hD.card_automizer_le (twoCentral_le X) hD.LN
  have hC3 : Nat.card ↥(img _ f Bs ⊓ Subgroup.centralizer
      ((((img _ f X).subtype.comp ψ₀).comp (MulAut.conj c).toMonoidHom).range : Set Q)) ≤ 3 := by
    rw [hrange, hD.cent hperfL le_rfl]
    exact hcentBsX
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hKu : Nat.card Kˣ = 3 := by
    have h := Nat.card_units K
    rw [hK4] at h
    simpa using h
  have hcube : ∀ c : Kˣ, c ^ 3 = 1 := fun c => by
    have := pow_card_eq_one' (G := Kˣ) (x := c)
    rwa [hKu] at this
  let a0 : Fin 6 := ⟨0, by omega⟩
  let a1 : Fin 6 := ⟨1, by omega⟩
  have ha01 : a0 ≠ a1 := by
    intro h
    have := congrArg Fin.val h
    simp [a0, a1] at this
  let rbar : MulAut ↥(img _ f Bs) :=
    ((ε (Equiv.swap a0 a1) : ↥(ggAutomizer (img _ f X) (img _ f Bs))) : MulAut ↥(img _ f Bs))
  have hrbarA : rbar ∈ ggAutomizer (img _ f X) (img _ f Bs) := (ε (Equiv.swap a0 a1)).2
  have hrbarRefl : GGIsReflection 3 rbar := hεrefl a0 a1 ha01
  have hrbar2 : ∀ a, rbar (rbar a) = a := fun a => by
    have h := congrArg (fun φ : MulAut ↥(img _ f Bs) => φ a) hrbarRefl.1
    simpa [pow_two] using h
  have hcomm : ∀ a b : ↥(img _ f Bs), a * b = b * a :=
    fun a b => hlocal.bstar.2.1.1.is_comm.comm a b
  obtain ⟨r₀, hr₀A, hr₀refl, hr₀rbar⟩ :=
    hD.exists_lift_reflection (twoCentral_le X) hD.LN hrbarA hrbarRefl
  have hfix : ∀ z ∈ twoCentral X, (∀ h ∈ ggHyperplane Bs r₀, h * z = z * h) → z = 1 := by
    rcases h3pow hAL with h3pow | hZ
    · have h3pow' : 3 ^ 6 ≤ Nat.card ↥(img _ f Bs) := by
        rw [hD.card_img le_rfl]
        exact h3pow
      obtain ⟨δ, hδ⟩ := exists_ggNSDetChar h' (by norm_num : 2 ^ 1 + 1 ∣ 6)
      obtain ⟨b₁, hb₁⟩ := ggNSDet_exists_ne_one h' hK4 hc hδ hC3 h3pow'
      have hδinv : ∀ a, δ (rbar a) = δ a := fun a =>
        ggNSDetChar_automizer h' hδ (by rw [hrange]; exact hrbarA) a
      obtain ⟨h₁, hh₁fix, hh₁δ⟩ := exists_fixed_det_ne_one hcomm rbar hrbar2 δ hδinv hcube hb₁
      obtain ⟨h₀, rfl⟩ := hD.tau.surjective h₁
      have hh₀fix : r₀ h₀ = h₀ := by
        apply hD.tau.injective
        rw [← congr_apply_tau hD.tau r₀ h₀, hr₀rbar]
        exact hh₁fix
      have hh₀H : (h₀ : G) ∈ ggHyperplane Bs r₀ := Subgroup.mem_map.2 ⟨h₀, hh₀fix, rfl⟩
      intro z hz hcz
      have hb0 : (h₀ : G) ∈ Bs := h₀.2
      have hbN : (h₀ : G) ∈ Subgroup.normalizer (X : Set G) := hBsN hb0
      obtain ⟨g, hg⟩ := h'.acts ((hD.tau h₀ : ↥(img _ f Bs)) : Q) (hD.tau h₀).2
      have hdet : Matrix.GeneralLinearGroup.det g = δ (hD.tau h₀) := hδ (hD.tau h₀) g hg
      let σL : MulAut ↥X := X.normalizerMonoidHom ⟨(h₀ : G), hbN⟩
      have hτN : f ⟨(h₀ : G), hD.BsN hb0⟩ ∈
          Subgroup.normalizer ((img _ f X : Subgroup Q) : Set Q) := hD.f_mem_normalizer_img hBsN hb0
      let τL : MulAut ↥(img _ f X) := (img _ f X).normalizerMonoidHom ⟨f ⟨(h₀ : G), hD.BsN hb0⟩, hτN⟩
      let ψc : Su K 2 1 6 →* ↥(img _ f X) := ψ₀.comp (MulAut.conj c).toMonoidHom
      have hzL : z ∈ X := twoCentral_le X hz
      have hzker : (⟨z, hzL⟩ : ↥X) ∈ hD.fL.ker := (hD.fL_eq_one_iff _).2 hz
      have hres := hU K hK ↥X ↥(img _ f X) hD.fL ψc σL τL g hperfL hD.fL_surjective
        (fun u hu l' => Subgroup.mem_center_iff.1
          (hD.mem_center_of_mem ((hD.fL_eq_one_iff u).1 hu)) l')
        (fun u hu => by
          obtain ⟨k, hk⟩ := hD.Z2 _ ((hD.fL_eq_one_iff u).1 hu)
          exact ⟨k, Subtype.ext (by simpa using hk)⟩)
        (hψ₀surj.comp (MulAut.conj c).surjective)
        (fun s hs => h'.ker (by
          rw [MonoidHom.mem_ker] at hs ⊢
          exact congrArg Subtype.val hs))
        (fun l => Subtype.ext (by
          have e : (⟨((σL l : ↥X) : G), hD.LN (σL l).2⟩ : ↥(Subgroup.normalizer (X : Set G))) =
              ⟨(h₀ : G), hD.BsN hb0⟩ * ⟨(l : G), hD.LN l.2⟩ * ⟨(h₀ : G), hD.BsN hb0⟩⁻¹ := rfl
          change f ⟨((σL l : ↥X) : G), hD.LN (σL l).2⟩ =
            f ⟨(h₀ : G), hD.BsN hb0⟩ * f ⟨(l : G), hD.LN l.2⟩ * (f ⟨(h₀ : G), hD.BsN hb0⟩)⁻¹
          rw [e, map_mul, map_mul, map_inv]))
        hg.1 (by rw [hdet]; exact hh₁δ)
        (fun s => by
          obtain ⟨y', hy', hby⟩ := hg.2 s
          refine ⟨y', hy', Subtype.ext ?_⟩
          exact hby)
        ⟨z, hzL⟩ hzker (Subtype.ext (by
          show (h₀ : G) * z * (h₀ : G)⁻¹ = z
          rw [mul_inv_eq_iff_eq_mul]
          exact hcz _ hh₀H))
      exact congrArg Subtype.val hres
    · intro z hz _
      have hzc : (⟨z, twoCentral_le X hz⟩ : ↥X) ∈ Subgroup.center ↥X :=
        Subgroup.mem_center_iff.2 fun l => Subtype.ext (twoCentral_central hz l l.2)
      rw [hZ, Subgroup.mem_bot] at hzc
      exact congrArg Subtype.val hzc
  have hsix : Nat.card ↥(ggRankOneIn X Bs r₀) = 6 := by
    rw [← hD.card_rankOneIn hfix, hr₀rbar]
    have hblk := hεblock a0 a1 ha01
    show Nat.card ↥(ggRankOneIn (img _ f X) (img _ f Bs)
      ((ε (Equiv.swap a0 a1) : ↥(ggAutomizer (img _ f X) (img _ f Bs))) : MulAut ↥(img _ f Bs))) = 6
    rw [hblk]
    exact card_ggSuPairBlock_map_zero_one (by norm_num) hK h'.ker
  exact ⟨r₀, hr₀A, hr₀refl, hsix⟩

theorem ggNsq2_exists_rankOne_of_or
    (hU : GGU62OuterDiagInput) (hTB : GGTBFixInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hdvd : p ∣ 2 ^ 1 + 1)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hbs : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (h3pow : 720 ≤ Nat.card ↥(ggAutomizer L Bs) →
      3 ^ 6 ≤ Nat.card ↥Bs ∨ Subgroup.center ↥L = ⊥) :
    ∃ r ∈ ggAutomizer L Bs, GGIsReflection p r ∧ Nat.card ↥(ggRankOneIn L Bs r) = 6 := by
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hcfg
  have hp3 : p = 3 := by
    have h3 : p ∣ 3 := by simpa using hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
  subst hp3
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1
  have hBsExp : ∀ b ∈ Bs, b ^ 3 = 1 := hconf.2.1.2.1.2
  have hS : LargeEvenSStar 3 B x L := hconf.1.2.2.2.2.2.2.1
  have hx : x ∈ Bs := hconf.2.1.1 hS.2.1
  obtain ⟨y, K', hN⟩ := exists_ggNbr hconf.1.2.2.2.2.2.2.2 hconf.2.2
  have hrefl : GGReflGenerated 3 (ggAutomizer K' Bs) := hcfg.2.1 y K' hN
  have hle : Bs ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.zpowers x := by
    intro b hb
    obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.1 hb
    have hbL : L ≤ Subgroup.centralizer ({b} : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hbC l hl).symm
    have hstab := ggAutomizer_le_stabilizer_of_centralizes hbB hbL
    exact hTB G 3 B Bs x L D J hconf hcfg.1.2.1 hcfg.1.2.2.1 hcfg.1.2.2.2.1 y K' hN hrefl
      (Or.inr hcfg.2.1) ⟨b, hbB⟩ (fun φ hφ => MulAction.mem_stabilizer_iff.1 (hstab hφ))
  have hC3 : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 :=
    calc Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card ↥(Subgroup.zpowers x) :=
          Subgroup.card_le_of_le hle
      _ ≤ 3 := by
          rw [Nat.card_zpowers]
          exact orderOf_le_of_pow_eq_one (by norm_num) (hBsExp x hx)
  exact ggNsq2Member_exists_rankOne_of_or hU hcfg (ggNSPosPD_routeCfg_cent_L hconf) hC3 hK hdvd θ hperf
    hBsN hbs h3pow

theorem ggNsq2_exists_rankOne
    (hU : GGU62OuterDiagInput) (hTB : GGTBFixInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hdvd : p ∣ 2 ^ 1 + 1)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hbs : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (h3pow : 720 ≤ Nat.card ↥(ggAutomizer L Bs) → 3 ^ 6 ≤ Nat.card ↥Bs) :
    ∃ r ∈ ggAutomizer L Bs, GGIsReflection p r ∧ Nat.card ↥(ggRankOneIn L Bs r) = 6 :=
  ggNsq2_exists_rankOne_of_or hU hTB hcfg hK hdvd θ hperf hBsN hbs fun h => Or.inl (h3pow h)

theorem ggNsq2_core
    (hU : GGU62OuterDiagInput) (hTB : GGTBFixInput) (hWA : GGTBFixNbrXInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    {m : ℕ} {σ : Fin m ≃ ι} (hM : M = (CoxeterMatrix.A m).reindex σ)
    (hno6 : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hdvd : p ∣ 2 ^ 1 + 1)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hbs : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hcfg
  have hp3 : p = 3 := by
    have h3 : p ∣ 3 := by simpa using hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
  subst hp3
  have h3pow : 720 ≤ Nat.card ↥(ggAutomizer L Bs) → 3 ^ 6 ≤ Nat.card ↥Bs := by
    intro hAL
    have hlt := ggPhanStrict_card_lt_join_of_wA hWA hcfg
    have hJoin : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) = (m + 1).factorial := by
      rw [← Nat.card_congr e.toEquiv, hM, card_coxeterGroup_reindex, l05nK3a_card_coxeterA]
    have hm7 : 7 ≤ m + 1 := by
      by_contra hlt7
      have h1 : (m + 1).factorial ≤ Nat.factorial 6 := Nat.factorial_le (by omega)
      have h6 : Nat.factorial 6 = 720 := by decide
      rw [hJoin] at hlt
      omega
    have h7dvd : 7 ∣ Nat.card ↥(ggAutomizerJoin L Bs 𝒦) := by
      rw [hJoin]
      exact Nat.dvd_factorial (by norm_num) hm7
    exact three_pow_six_le_card_of_seven_dvd hconf.2.1.2.1 h7dvd
  obtain ⟨r₀, hr₀A, hr₀refl, hsix⟩ :=
    ggNsq2_exists_rankOne hU hTB hcfg hK hdvd θ hperf hBsN hbs h3pow
  have hle3A : ∀ i j : Fin m, i ≠ j → (CoxeterMatrix.A m).M i j ≤ 3 := by
    intro i j hij
    simp only [CoxeterMatrix.A, Matrix.of_apply]
    split_ifs <;> omega
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
    intro i j hij
    rw [hM, CoxeterMatrix.reindex_apply]
    exact hle3A _ _ (fun h => hij (σ.symm.injective h))
  have hr₀C : r₀ ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr₀A) hr₀refl
  exact hno6 r₀ hr₀A hr₀C hsix

theorem ggNsq2L_of_u62
    (hU : GGU62OuterDiagInput) (hTB : GGTBFixInput) (hWA : GGTBFixNbrXInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    {m : ℕ} {σ : Fin m ≃ ι} (hM : M = (CoxeterMatrix.A m).reindex σ)
    (hno6 : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) :
    False := by
  obtain ⟨K, hf, hfin, lab, m', θ, hK, h4m, hmrank, hSide, hdvd, hperf, hlab, hBsN, hbs⟩ :=
    ggNSLieN3A_esuCore hmark (fun p lab hl => hl.1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := lab.n) hK
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨-, hn1, hr5⟩ := hSide
  change n = 1 at hn1
  change rank = 5 at hr5
  change m' = rank + 1 at hmrank
  subst hn1
  subst hr5
  have hm6 : m' = 6 := by omega
  subst hm6
  exact ggNsq2_core hU hTB hWA hcfg hpres hM hno6 hK hdvd θ hperf hBsN hbs

theorem ggSecFiveNSQ2LInput_of_u62
    (hU : GGU62OuterDiagInput) : GGSecFiveNSQ2LInput := by
  intro hTB hWA _ _ G _ _ p B Bs x L D J 𝒦 hcfg _ ι M e hpres hA hno6 hmark
  obtain ⟨m, σ, -, hM⟩ := hA
  exact ggNsq2L_of_u62 hU hTB hWA hcfg hpres hM hno6 hmark

end CFSG.StandardType

end
