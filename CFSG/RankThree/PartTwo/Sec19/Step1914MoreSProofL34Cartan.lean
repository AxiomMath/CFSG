module

public import CFSG.RankThree.PartTwo.Sec19.Step1914MoreSProofL34
public import CFSG.RankThree.PartTwo.Sec19.Step1914MoreSProofL34Model
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item138ProofSylow
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec15.NoModNineTools
import CFSG.RankThree.PartTwo.Sec18.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projSL projImage)
open CFSG.Assembly.LowTwoRank
open Matrix (GeneralLinearGroup ProjGenLinGroup)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi zPi PiField ModThree Type123 stdTypeC)

namespace Step1914MoreSProof

theorem eq_four_of_card {π : Bool} {q : ℕ} (hq : 2 ≤ q)
    (h : q ^ 3 * (q ^ 2 - 1) * cond π (q ^ 3 - 1) (q ^ 3 + 1) = 60480) : π = true ∧ q = 4 := by
  have hq4 : q ≤ 4 := by
    by_contra h5
    push Not at h5
    have h1 : 125 ≤ q ^ 3 := by
      calc 125 = 5 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left h5 3
    have h2 : 24 ≤ q ^ 2 - 1 := by
      have : 25 ≤ q ^ 2 := by
        calc 25 = 5 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left h5 2
      omega
    have h3 : 124 ≤ cond π (q ^ 3 - 1) (q ^ 3 + 1) := by
      cases π <;> simp only [Bool.cond_true, Bool.cond_false] <;> omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega
  interval_cases q <;> cases π <;> simp_all

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem not_inner_of_type3 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K) (hy3 : Type123 π (p ^ f) K y 3) :
    ¬ ∃ l ∈ slPi π 3 (p ^ f) K, ∀ m ∈ slPi π 3 (p ^ f) K, y * m * y⁻¹ = l * m * l⁻¹ :=
  CFSG.RankThree.PartTwo.Sec4.not_inner_of_type3 hK hq hyH hy3

theorem mk_not_mem_of_type3 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K) (hy3 : Type123 π (p ^ f) K y 3) :
    ProjGenLinGroup.mk y ∉ projImage (slPi π 3 (p ^ f) K) := by
  rintro ⟨s, hs, hsy⟩
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hsy
  refine not_inner_of_type3 hK hq hyH hy3 ⟨s, hs, fun m _ => ?_⟩
  rw [← hu]
  have hc := Sec4.commute_of_mem_statedScalars ⟨u, rfl⟩ m
  calc s * GeneralLinearGroup.scalar (Fin 3) u * m * (s * GeneralLinearGroup.scalar (Fin 3) u)⁻¹
      = s * (GeneralLinearGroup.scalar (Fin 3) u * m) *
        (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ * s⁻¹ := by group
    _ = s * m * s⁻¹ := by rw [← hc]; group

section Core

variable {G : Type} [Group G] [Finite G]

theorem exists_cartan_of_model {A L E : Subgroup G} {c x : G} (hF : L34Facts A L E c)
    (hE : IsE27 E) (hEeq : E = Subgroup.zpowers c ⊔ (E ⊓ L)) (hxA : x ∈ A)
    {p f : ℕ} {K : Type} [Field K] (hK : PiField true p f K) (hq : ModThree true (p ^ f))
    (h4 : p ^ f = 4) (e : L ⧸ aschbacherSolvableCore 3 L ≃* projImage (slPi true 3 (p ^ f) K))
    {y : GL (Fin 3) K} (hy3 : Type123 true (p ^ f) K y 3)
    (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hxy : ∀ z : L ⧸ aschbacherSolvableCore 3 L,
      ((e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hx⟩) z) :
        projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) :
    ∃ F : Subgroup G, F ≤ E ⊔ A ∧ c ∈ F ∧ CFSG.Assembly.IsElemAbelian 3 F ∧
      Nat.card F = 27 ∧ ¬ F ≤ Subgroup.zpowers c ⊔ L ∧
      Late.sectionCentralizer F L ((aschbacherSolvableCore 3 L).map L.subtype) =
        (Subgroup.zpowers c : Set G) ∧
      Sec4.IsTypeCOn F L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hD, hcL, hcE, hcA, hco, -, -, -, hB9, hP3, hPN, hPNB, hEAC, hAEN, hP81, -⟩ := hF
  have hc3 : c ^ 3 = 1 := by rw [← hco]; exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := fun h1 => hcL (h1 ▸ L.one_mem)
  have hA : CFSG.Assembly.IsElemAbelian 3 A := hD.isElemAbelian
  have hx3 : x ^ 3 = 1 := hA.2 x hxA
  have := hK.finite
  have hK4 : Nat.card K = 4 := by rw [hK.card, h4]; rfl
  have hq2 : 2 < p ^ f := by omega
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) ProjGenLinGroup.mk_surjective
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)
  have hSLn : (slPi true 3 (p ^ f) K).Normal := ⟨fun s hs g => by
    rw [Sec4.mem_slPi_true] at hs ⊢
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hs, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]⟩
  have hPSn : (projImage (slPi true 3 (p ^ f) K)).Normal :=
    hSLn.map ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  set κ : ProjGenLinGroup (Fin 3) K →* MulAut (projImage (slPi true 3 (p ^ f) K)) :=
    MulAut.conjNormal with hκdef
  have hκapp : ∀ (w : ProjGenLinGroup (Fin 3) K) (m : projImage (slPi true 3 (p ^ f) K)),
      ((κ w m : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        w * m * w⁻¹ := fun w m =>
    MulAut.conjNormal_apply w m
  have hκ : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    refine eq_one_of_conj_eq_self hK hq hq2 fun s hs => ?_
    have h1 := congrArg (fun σ : MulAut (projImage (slPi true 3 (p ^ f) K)) =>
      ((σ ⟨s, hs⟩ : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K)) hw
    simpa [hκapp] using h1
  set act : Subgroup.normalizer (L : Set G) →* MulAut (projImage (slPi true 3 (p ^ f) K)) :=
    (MulAut.congr e).toMonoidHom.comp ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom)
    with hactdef
  have hact : ∀ (g : Subgroup.normalizer (L : Set G)) (m : projImage (slPi true 3 (p ^ f) K)),
      act g m = e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom g) (e.symm m)) :=
    fun _ _ => rfl
  have hactL : ∀ (l : G) (hl : l ∈ L) (hlN : l ∈ Subgroup.normalizer (L : Set G)),
      act ⟨l, hlN⟩ = κ ((e (⟨l, hl⟩ : L) : projImage (slPi true 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) := by
    intro l hl hlN
    ext m
    rw [hact, hκapp, Sec15.thetaQuotMulAut_eq_conj hlN ⟨l, hl⟩ (fun _ => rfl), map_mul, map_mul,
      map_inv, MulEquiv.apply_symm_apply]
    rfl
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun l hl =>
      hLc l hl)
  have hnc : L.normalizerMonoidHom ⟨c, hcN⟩ = 1 := by
    ext l
    rw [Sec4.normalizerMonoidHom_apply_coe, ← hLc l l.2, mul_inv_cancel_right]
    rfl
  have hactc : act ⟨c, hcN⟩ = 1 := by
    rw [hactdef, MonoidHom.comp_apply, MonoidHom.comp_apply, hnc, map_one, map_one]
  have hactx : act ⟨x, hx⟩ = κ (ProjGenLinGroup.mk y) := by
    ext m
    rw [hact, hκapp, hxy, MulEquiv.apply_symm_apply]
  set P := E ⊔ Subgroup.zpowers x with hPdef
  have hPEA : P ≤ E ⊔ A := sup_le le_sup_left (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right hxA))
  have hPN' : P ≤ Subgroup.normalizer (L : Set G) := hPEA.trans hPN
  set S : Subgroup G := (κ.range.comap act).map (Subgroup.normalizer (L : Set G)).subtype
    with hSdef
  have hmemS : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)), act ⟨g, hg⟩ ∈ κ.range →
      g ∈ S := fun g hg h => ⟨⟨g, hg⟩, h, rfl⟩
  have hSmem : ∀ g ∈ S, ∀ hg : g ∈ Subgroup.normalizer (L : Set G), act ⟨g, hg⟩ ∈ κ.range := by
    rintro _ ⟨n, hn, rfl⟩ hg
    exact hn
  have hLS : L ≤ S := fun l hl => hmemS l (Subgroup.le_normalizer hl)
    ⟨_, (hactL l hl (Subgroup.le_normalizer hl)).symm⟩
  have hES : E ≤ S := by
    rw [hEeq]
    exact sup_le (Subgroup.zpowers_le.mpr (hmemS c hcN ⟨1, by rw [map_one, hactc]⟩))
      (inf_le_right.trans hLS)
  have hPS : P ≤ S := sup_le hES (Subgroup.zpowers_le.mpr (hmemS x hx ⟨_, hactx.symm⟩))
  have hrange : ∀ g : P, act (Subgroup.inclusion hPN' g) ∈ κ.range := fun g =>
    hSmem g.1 (hPS g.2) _
  set ψ : P →* ProjGenLinGroup (Fin 3) K := (MonoidHom.ofInjective hκ).symm.toMonoidHom.comp
    ((act.comp (Subgroup.inclusion hPN')).codRestrict κ.range hrange) with hψdef
  have hψ : ∀ g : P, κ (ψ g) = act (Subgroup.inclusion hPN' g) := by
    intro g
    have h1 := MonoidHom.ofInjective_apply hκ (x := ψ g)
    rw [hψdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hψeq : ∀ (g : P) (w : ProjGenLinGroup (Fin 3) K),
      κ w = act (Subgroup.inclusion hPN' g) → ψ g = w := fun g w h =>
    hκ ((hψ g).trans h.symm)
  have hcP : c ∈ P := Subgroup.mem_sup_left hcE
  have hxP : x ∈ P := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hψL : ∀ (g : P) (hgL : (g : G) ∈ L), ψ g =
      ((e (⟨g, hgL⟩ : L) : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) :=
    fun g hgL => hψeq g _ (hactL g hgL (hPN' g.2)).symm
  have hψc : ψ ⟨c, hcP⟩ = 1 := hψeq _ 1 (by rw [map_one]; exact hactc.symm)
  have hψx : ψ ⟨x, hxP⟩ = ProjGenLinGroup.mk y := hψeq _ _ hactx.symm
  set BL : Subgroup P := (E ⊓ L).subgroupOf P with hBLdef
  have hBLP : E ⊓ L ≤ P := inf_le_left.trans le_sup_left
  have hBLp : IsPGroup 3 ((E ⊓ L).subgroupOf L) :=
    (IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num) :
      IsPGroup 3 (E ⊓ L : Subgroup G)).comap_subtype
  have hinjBL : Set.InjOn ψ BL := by
    intro g₁ hg₁ g₂ hg₂ h12
    have hg₁L : (g₁ : G) ∈ L := (Subgroup.mem_subgroupOf.mp hg₁).2
    have hg₂L : (g₂ : G) ∈ L := (Subgroup.mem_subgroupOf.mp hg₂).2
    rw [hψL g₁ hg₁L, hψL g₂ hg₂L] at h12
    have h1 := e.injective (Subtype.ext h12)
    have h2 := injOn_mk_of_isPGroup Nat.prime_three hBLp
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hg₁))
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hg₂)) h1
    have h3 : (g₁ : G) = g₂ := congrArg (fun z : L => (z : G)) h2
    exact Subtype.ext h3
  set H : Subgroup (ProjGenLinGroup (Fin 3) K) := BL.map ψ with hHdef
  have hH9 : Nat.card H = 9 := by
    rw [hHdef, Sec13.card_map_eq_of_injOn _ hinjBL, hBLdef, ← hB9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBLP).toEquiv
  have hψxH : ψ ⟨x, hxP⟩ ∉ H := by
    rintro ⟨g, hg, hgx⟩
    have hgL : (g : G) ∈ L := (Subgroup.mem_subgroupOf.mp hg).2
    rw [hψx, hψL g hgL] at hgx
    exact mk_not_mem_of_type3 hK hq (Sec4.mem_glPi_true _ y) hy3 (hgx ▸ (e _).2)
  have hPp : IsPGroup 3 P := hP3.to_le hPEA
  set R := ψ.range with hRdef
  have hRp : IsPGroup 3 R := by
    rintro ⟨_, g, rfl⟩
    obtain ⟨k, hk⟩ := hPp g
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← map_pow, hk, map_one, Subgroup.coe_one]
  have hHR : H ≤ R := by
    rintro _ ⟨g, -, rfl⟩
    exact ⟨g, rfl⟩
  have hR27 : Nat.card R = 27 := by
    have h9 : 9 ∣ Nat.card R := hH9 ▸ Subgroup.card_dvd_of_le hHR
    have hle : Nat.card R ≤ 3 ^ 3 := by
      have := Item138Proof.card_le_of_isPGroup (le_top : R ≤ ⊤) hRp
      rwa [Subgroup.card_top, factorization_card_pgl_three_of_card_four hK4] at this
    have hne : Nat.card R ≠ 9 := by
      intro h
      apply hψxH
      rw [Subgroup.eq_of_le_of_card_ge hHR (by rw [h, hH9])]
      exact ⟨_, rfl⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
    rw [hk] at h9 hle hne ⊢
    have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    have hk2 : 2 ≤ k := by
      by_contra hk2
      push Not at hk2
      interval_cases k <;> norm_num at h9
    interval_cases k
    · exact absurd rfl hne
    · rfl
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf 3 R (⊤ : Subgroup (ProjGenLinGroup (Fin 3) K)) :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top
      (by rw [hR27, Subgroup.card_top, factorization_card_pgl_three_of_card_four hK4]; norm_num)
  obtain ⟨n, -, hn⟩ := Sec18.exists_map_conj_eq_of_isSylowOf (isSylowOf_stdSylow hK hq hK4) hRsyl
  set T := (stdTorus K).map (MulAut.conj n).toMonoidHom with hTdef
  have hTR : T ≤ R := by
    rw [hn]
    exact Subgroup.map_mono le_sup_left
  have hT9 : Nat.card T = 9 := by
    rw [hTdef, Subgroup.card_map_of_injective (MulAut.conj n).injective, card_stdTorus hK hq]
  have hcomm : ∀ a ∈ Subgroup.zpowers c, ∀ b ∈ E ⊓ L, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (hLc b hb.2).symm i).eq
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).2
  have hψE : ∀ g : P, (g : G) ∈ E → ψ g ∈ H := by
    intro g hgE
    have hg' : (g : G) ∈ ((Subgroup.zpowers c ⊔ (E ⊓ L) : Subgroup G) : Set G) := hEeq ▸ hgE
    rw [hset] at hg'
    obtain ⟨a, ha, b, hb, hab⟩ := hg'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbP : b ∈ P := hBLP hb
    have hg : g = ⟨c, hcP⟩ ^ i * ⟨b, hbP⟩ := Subtype.ext (by simpa using hab.symm)
    rw [hg, map_mul, map_zpow, hψc, one_zpow, one_mul]
    exact ⟨⟨b, hbP⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hxE : x ∉ E := fun h => hψxH (hψE ⟨x, hxP⟩ h)
  have hP81 : Nat.card P = 81 := by
    have hdvd : Nat.card P ∣ 3 ^ 4 := by
      rw [show (3 : ℕ) ^ 4 = 81 by norm_num, ← hP81]
      exact Subgroup.card_dvd_of_le hPEA
    have hE27 : 27 ∣ Nat.card P := hE.2 ▸ Subgroup.card_dvd_of_le (le_sup_left : E ≤ P)
    have hne : Nat.card P ≠ 27 := by
      intro h27
      apply hxE
      rw [Subgroup.eq_of_le_of_card_ge (le_sup_left : E ≤ P) (by rw [h27, hE.2])]
      exact hxP
    obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hk] at hE27 hne ⊢
    interval_cases k
    · norm_num at hE27
    · norm_num at hE27
    · norm_num at hE27
    · exact absurd rfl hne
    · rfl
  have hker3 : Nat.card ψ.ker = 3 := by
    have h1 := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker, hP81] at h1
    change Nat.card ψ.ker * Nat.card R = 81 at h1
    rw [hR27] at h1
    omega
  have hker : ψ.ker = (Subgroup.zpowers c).subgroupOf P := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro g hg
      rw [Subgroup.mem_subgroupOf] at hg
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hg
      have : g = ⟨c, hcP⟩ ^ i := Subtype.ext (by simpa using hi.symm)
      rw [MonoidHom.mem_ker, this, map_zpow, hψc, one_zpow]
    · rw [hker3, ← card_zpowers_of_pow_three hc3 hc1]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.zpowers_le.mpr hcP)).toEquiv).ge
  set F' : Subgroup P := T.comap ψ with hF'def
  set F : Subgroup G := F'.map P.subtype with hFdef
  have hF'T : F'.map ψ = T := by
    rw [hF'def, Subgroup.map_comap_eq, inf_eq_right.mpr hTR]
  have hkerF' : ψ.ker ≤ F' := fun g hg => by
    rw [MonoidHom.mem_ker] at hg
    change ψ g ∈ T
    rw [hg]
    exact T.one_mem
  have hF'27 : Nat.card F' = 27 := by
    have h1 := Step1914TriProof.card_map_mul_card_ker_subgroupOf ψ F'
    rw [hF'T, hT9] at h1
    have h2 : Nat.card (ψ.ker.subgroupOf F') = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerF').toEquiv, hker3]
    rw [h2] at h1
    omega
  have hF27 : Nat.card F = 27 := by
    rw [hFdef, Subgroup.card_map_of_injective P.subtype_injective, hF'27]
  have hFP : F ≤ P := Subgroup.map_subtype_le F'
  have hmemF : ∀ g : P, (g : G) ∈ F ↔ g ∈ F' := fun g => by
    constructor
    · rintro ⟨g', hg', hgg'⟩
      rwa [show g = g' from Subtype.ext hgg'.symm]
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hcF : c ∈ F := (hmemF ⟨c, hcP⟩).mpr (show ψ ⟨c, hcP⟩ ∈ T by rw [hψc]; exact T.one_mem)
  set φ : P →* Subgroup.normalizer (L : Set G) ⧸ L.subgroupOf (Subgroup.normalizer (L : Set G)) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hPN') with hφdef
  have hφ1 : ∀ g : P, φ g = 1 → (g : G) ∈ L := fun g h => by
    rw [hφdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact h
  have hφL : ∀ g : P, (g : G) ∈ L → φ g = 1 := fun g h => by
    rw [hφdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h
  have hpow : ∀ g : P, (g : G) ^ 3 = 1 → g ^ 3 = 1 := fun g h =>
    Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])
  have hxc : x * c = c * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (hEAC (Subgroup.mem_sup_right hxA))
  set Q := Subgroup.zpowers (φ ⟨c, hcP⟩) ⊔ Subgroup.zpowers (φ ⟨x, hxP⟩) with hQdef
  have hQab : CFSG.Assembly.IsElemAbelian 3 Q :=
    Sec13.isElemAbelian_zpowers_sup (by rw [← map_pow, hpow _ hc3, map_one])
      (by rw [← map_pow, hpow _ hx3, map_one])
      (by rw [← map_mul, ← map_mul]; exact congrArg φ (Subtype.ext hxc.symm))
  have hφQ : ∀ g : P, φ g ∈ Q := by
    have hle : P ≤ (Q.comap φ).map P.subtype := by
      refine sup_le (hEeq.le.trans (sup_le ?_ ?_)) ?_
      · exact Subgroup.zpowers_le.mpr
          ⟨⟨c, hcP⟩, Subgroup.mem_sup_left (Subgroup.mem_zpowers _), rfl⟩
      · intro b hb
        refine ⟨⟨b, hBLP hb⟩, ?_, rfl⟩
        change φ ⟨b, hBLP hb⟩ ∈ Q
        rw [hφL _ hb.2]
        exact Q.one_mem
      · exact Subgroup.zpowers_le.mpr
          ⟨⟨x, hxP⟩, Subgroup.mem_sup_right (Subgroup.mem_zpowers _), rfl⟩
    intro g
    obtain ⟨g', hg', hgg'⟩ := hle g.2
    rw [show g = g' from Subtype.ext hgg'.symm]
    exact hg'
  have htriv : ∀ g : P, ψ g = 1 → φ g = 1 → g = 1 := by
    intro g h1 h2
    have hgc : g ∈ ψ.ker := h1
    rw [hker] at hgc
    have hg : (g : G) ∈ Subgroup.zpowers c ⊓ L := ⟨hgc, hφ1 g h2⟩
    rw [Sec13.zpowers_inf_eq_bot hc3 hcL, Subgroup.mem_bot] at hg
    exact Subtype.ext hg
  have hTab : CFSG.Assembly.IsElemAbelian 3 T :=
    Sec13.isElemAbelian_map isElemAbelian_stdTorus (MulAut.conj n).toMonoidHom
  have hcommT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    have := hTab.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : T) ⟨b, hb⟩)
  have hcommQ : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    have := hQab.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Q) ⟨b, hb⟩)
  have hcommP : ∀ a b : P, ψ a ∈ T → ψ b ∈ T → a * b = b * a := by
    intro a b ha hb
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 := htriv _
      (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcommT _ ha _ hb]; group)
      (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcommQ _ (hφQ a) _ (hφQ b)]; group)
    rw [← commutatorElement_def] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hFab : CFSG.Assembly.IsElemAbelian 3 F := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => ?_⟩
    · have h1 := congrArg Subtype.val (hcommP ⟨a, hFP a.2⟩ ⟨b, hFP b.2⟩ ((hmemF _).mp a.2)
        ((hmemF _).mp b.2))
      exact h1
    · have h1 : (⟨g, hFP hg⟩ : P) ^ 3 = 1 := htriv _
        (by rw [map_pow]; exact hTab.2 _ ((hmemF _).mp hg))
        (by rw [map_pow]; exact hQab.2 _ (hφQ _))
      have h2 := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  have hcommL : ∀ a ∈ Subgroup.zpowers c, ∀ b ∈ L, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (hLc b hb).symm i).eq
  have hsetL := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommL).2
  have hFout : ¬ F ≤ Subgroup.zpowers c ⊔ L := by
    intro hle
    obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
    refine stdTorus_not_le hK4 hτ hτ1 (p ^ f) fun t ht => ?_
    have hnt : n * t * n⁻¹ ∈ T := ⟨t, ht, rfl⟩
    rw [← hF'T] at hnt
    obtain ⟨g, hgF', hg⟩ := hnt
    have hgcL : (g : G) ∈ ((Subgroup.zpowers c ⊔ L : Subgroup G) : Set G) :=
      hle ((hmemF g).mpr hgF')
    rw [hsetL] at hgcL
    obtain ⟨a, ha, l, hl, hal⟩ := hgcL
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hlP : l ∈ P := by
      have hl' : l = (c ^ i)⁻¹ * g := by rw [← hal]; group
      rw [hl']
      exact P.mul_mem (P.inv_mem (P.zpow_mem hcP i)) g.2
    have hg' : g = ⟨c, hcP⟩ ^ i * ⟨l, hlP⟩ := Subtype.ext (by simpa using hal.symm)
    rw [hg', map_mul, map_zpow, hψc, one_zpow, one_mul, hψL ⟨l, hlP⟩ hl] at hg
    have h1 : n * t * n⁻¹ ∈ projImage (slPi true 3 (p ^ f) K) := hg ▸ (e _).2
    have h2 := hPSn.conj_mem _ h1 n⁻¹
    rwa [show n⁻¹ * (n * t * n⁻¹) * n⁻¹⁻¹ = t by group] at h2
  have hsec : Late.sectionCentralizer F L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf (hFP.trans hPN')]
    ext a
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    constructor
    · rintro ⟨haF, y, hy, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
      have h1 : act y = 1 := by
        rw [hactdef, MonoidHom.comp_apply, MonoidHom.comp_apply, hy, map_one]
      have h2 : ψ ⟨y, hFP haF⟩ = 1 := hκ (by rw [hψ, map_one]; exact h1)
      have h3 : (⟨y, hFP haF⟩ : P) ∈ ψ.ker := h2
      rw [hker] at h3
      exact h3
    · intro ha
      refine ⟨Subgroup.zpowers_le.mpr hcF ha, ?_⟩
      have hcT : c ∈ Sec4.thetaQuotCentralizer L :=
        ⟨⟨c, hcN⟩, by
          rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, hnc, map_one], rfl⟩
      exact Subgroup.zpowers_le.mpr hcT ha
  have hformula : ∀ (g : P) (z : L ⧸ aschbacherSolvableCore 3 L),
      ((e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom (Subgroup.inclusion hPN' g)) z) :
        projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ψ g * (e z : ProjGenLinGroup (Fin 3) K) * (ψ g)⁻¹ := by
    intro g z
    rw [← hκapp, hψ g, hact, MulEquiv.symm_apply_apply]
  obtain ⟨n₀, hn₀⟩ := ProjGenLinGroup.mk_surjective n
  set D : Subgroup (GL (Fin 3) K) := (stdTypeC K).map (MulAut.conj n₀).toMonoidHom with hDdef
  have hDT : D.map ProjGenLinGroup.mk = T := by
    rw [hDdef, hTdef, stdTorus, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, hn₀]
  have hTC : Sec4.IsTypeCOn F L := by
    refine ⟨true, p, f, K, inferInstance, hK, hq, e, D,
      isTypeC_map_conj (Sec4.isTypeC_stdTypeC hK hq) (Sec4.mem_glPi_true _ n₀), ?_, ?_⟩
    · intro τ hτ
      obtain ⟨h, hN, hhF, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
      have hgT : ψ ⟨h, hFP hhF⟩ ∈ T := (hmemF ⟨h, hFP hhF⟩).mp hhF
      rw [← hDT] at hgT
      obtain ⟨y, hyD, hy⟩ := hgT
      exact ⟨y, hyD, fun z => by rw [hy]; exact hformula ⟨h, hFP hhF⟩ z⟩
    · intro y hyD
      have hyT : ProjGenLinGroup.mk y ∈ T := hDT ▸ ⟨y, hyD, rfl⟩
      rw [← hF'T] at hyT
      obtain ⟨g, hgF', hg⟩ := hyT
      refine ⟨_, Sec4.mem_autThetaQuot_iff.mpr ⟨g, hPN' g.2, (hmemF g).mpr hgF', rfl⟩,
        fun z => ?_⟩
      rw [← hg]
      exact hformula g z
  exact ⟨F, hFP.trans hPEA, hcF, hFab, hF27, hFout, hsec, hTC⟩

end Core

end Step1914MoreSProof

open Step1914MoreSProof in
theorem step1914MoreL34Cartan
    (h131 : Item131) : Step1914MoreL34Cartan := by
  intro G _ _ A c L E M hctx hφ hEeq hdisj
  have hF := l34Facts_of h131 hctx hφ hEeq hdisj
  have hE := isE27_of_mem_partTwoE hctx.mem_partTwoT.1
  have hAE := isE27_of_mem_partTwoE hctx.mem_partTwoE
  have hA9 : Nat.card (A ⊓ L : Subgroup G) ≠ 9 := by
    intro h9
    have hle : A ⊓ L ≤ E ⊓ L := (inf_le_inf_right L le_sup_right).trans hF.inf_eq.ge
    have heq : A ⊓ L = E ⊓ L := Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hF.card_inf])
    have hEA : E ≤ A := by
      rw [hEeq]
      exact sup_le (Subgroup.zpowers_le.mpr hF.c_mem_A) (heq.symm.le.trans inf_le_left)
    have hEA' : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [hE.2, hAE.2])
    exact hctx.not_mem_partTwoT (hEA' ▸ hctx.mem_partTwoT)
  rcases cases131 h131 sporadicModels131 slTwoCenter hF.sec13 with ⟨-, h9, -⟩ | ⟨-, h9, -⟩ |
      ⟨-, -, -, x, hxA, hxT⟩ | ⟨hcL', -⟩
  · exact absurd h9 hA9
  · exact absurd h9 hA9
  · obtain ⟨hx, π, p, f, K, _, hK, hq, e, y, -, hy3, hxy⟩ := hxT
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨π₀, K₀, _, hK₀, hq₀, ⟨e₀⟩⟩ :=
      Sec13.exists_projImage_model (by norm_num : 1 ≤ 2) hF.isoLThreePi
    have hπ₀ : π₀ = true := by
      cases π₀
      · simp [ModThree] at hq₀
      · rfl
    subst hπ₀
    have hc₀ := card_projImage_slPi_mul_three hK₀ hq₀
    have hc := card_projImage_slPi_mul_three hK hq
    rw [← Nat.card_congr e₀.toEquiv, Nat.card_congr e.toEquiv] at hc₀
    have hcard : (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) *
        cond π ((p ^ f) ^ 3 - 1) ((p ^ f) ^ 3 + 1) = 60480 := by
      rw [← hc, hc₀]
      norm_num
    have hf : f ≠ 0 := by
      have := hK.one_le
      omega
    have hq2 : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow hf _)
    obtain ⟨rfl, h4⟩ := eq_four_of_card hq2 hcard
    exact exists_cartan_of_model hF hE hEeq hxA hK hq h4 e hy3 hx hxy
  · exact absurd hcL' hF.c_not_mem

theorem step1914MoreSL34_of
    (h131 : Item131) (htri : Step1914Tri) (h195 : Item195)
    (hSyl : Item138SylowN) (hS : Item138SN) : Step1914MoreSL34 :=
  step1914MoreSL34_of_cartan h131 htri h195 hSyl hS (step1914MoreL34Cartan h131)

end CFSG.RankThree.PartTwo.Sec19
