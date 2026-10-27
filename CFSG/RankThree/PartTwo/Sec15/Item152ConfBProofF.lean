module

public import CFSG.RankThree.PartTwo.Sec15.Item152StepsConf
public import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofFlag
public import CFSG.RankThree.PartTwo.Sec15.Item152GenProofX
import CFSG.RankThree.PartTwo.Sec10.Item109

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

namespace Proof152F

variable {G : Type} [Group G] [Finite G]

theorem card_frattini_quot_eq {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (htype : (IsElementaryAbelian p ↥P ∧ Nat.card P = p ^ 2) ∨
      (CFSG.IsExtraspecialPGroup p ↥P ∧ Nat.card P = p ^ 3)) :
    Nat.card (↥P ⧸ frattini ↥P) = p ^ 2 := by
  have hp : p.Prime := Fact.out
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini ↥P)
  rcases htype with ⟨hE, hcard⟩ | ⟨hE, hcard⟩
  · have : Fact (IsPGroup p ↥P) := ⟨IsPGroup.of_card hcard⟩
    have hΦ : frattini ↥P = ⊥ := frattini_eq_bot_of_isElementaryAbelian (p := p)
    have hc : Nat.card (frattini ↥P) = 1 := by rw [hΦ, Subgroup.card_bot]
    rw [hc, mul_one, hcard] at h
    exact h.symm
  · obtain ⟨-, -, hΦ, hZ⟩ := hE
    have hc : Nat.card (frattini ↥P) = p := by rw [hΦ, hZ]
    rw [hc, hcard, pow_succ] at h
    exact (Nat.eq_of_mul_eq_mul_right hp.pos h).symm

theorem pCore_two_le_theta (X : Type) [Group X] [Finite X] :
    CFSG.pCore 2 X ≤ aschbacherSolvableCore 3 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθ := solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hp2 : IsPGroup 2 (CFSG.pCore 2 X) := CFSG.pCore_isPGroup
  refine hθ.2.2.2.1 _ CFSG.pCore_normal ?_ ?_
  · have : Group.IsNilpotent (CFSG.pCore 2 X) := hp2.isNilpotent
    infer_instance
  · obtain ⟨k, hk⟩ := hp2.exists_card_eq
    rw [hk]
    intro h3
    have := Nat.prime_three.dvd_of_dvd_pow (h3.trans (dvd_refl _))
    omega

theorem oTwoOddIn_le_theta {X : Subgroup G}
    (hXs : IsSimpleGroup (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (h2 : 2 ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X)) :
    oTwoOddIn X ≤ (aschbacherSolvableCore 3 ↥X).map X.subtype := by
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  set O := (CFSG.oddCore (↥X ⧸ CFSG.pCore 2 ↥X)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥X))
    with hO
  have hO2 : CFSG.pCore 2 ↥X ≤ θ := pCore_two_le_theta ↥X
  let φ : ↥X ⧸ CFSG.pCore 2 ↥X →* ↥X ⧸ θ :=
    QuotientGroup.map _ _ (MonoidHom.id _) (by simpa using hO2)
  have hφ : ∀ x : ↥X, φ (QuotientGroup.mk' (CFSG.pCore 2 ↥X) x) = QuotientGroup.mk' θ x :=
    fun _ => rfl
  have hOn : (O.map (QuotientGroup.mk' θ)).Normal :=
    (Subgroup.Normal.comap (CFSG.oddCore_normal _) _).map _ (QuotientGroup.mk'_surjective θ)
  have hodd : Odd (Nat.card (O.map (QuotientGroup.mk' θ))) := by
    have heq : O.map (QuotientGroup.mk' θ) = (O.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).map φ :=
      by rw [Subgroup.map_map]; rfl
    have h1 : Nat.card (O.map (QuotientGroup.mk' θ)) ∣
        Nat.card (CFSG.oddCore (↥X ⧸ CFSG.pCore 2 ↥X)) := by
      rw [heq]
      exact (Subgroup.card_map_dvd _ _).trans
        (Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _))
    exact Odd.of_dvd_nat Sec10.odd_card_oddCore h1
  have hbot : O.map (QuotientGroup.mk' θ) = ⊥ := by
    rcases hXs.eq_bot_or_eq_top_of_normal (O.map (QuotientGroup.mk' θ)) with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at hodd
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨m, hm⟩ := h2
      omega
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact Subgroup.map_mono hbot

theorem oTwoP_le_theta {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) (X : Type) [Group X] [Finite X] :
    Sec4.oTwoP p X ≤ aschbacherSolvableCore 3 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθ := solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  set K := Sec4.oTwoP p X with hK
  set Q := CFSG.pCore 2 X with hQ
  have hKn : K.Normal := Subgroup.Normal.comap (CFSG.pCore_normal (p := p)) _
  have hQK : Q ≤ K := Sec4.pCore_two_le_oTwoP p X
  set f : K →* X ⧸ Q := (QuotientGroup.mk' Q).comp K.subtype with hf
  have hrange : f.range ≤ CFSG.pCore p (X ⧸ Q) := by
    rintro _ ⟨x, rfl⟩
    exact x.2
  have hker : f.ker = Q.subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have hrp : IsPGroup p f.range := (CFSG.pCore_isPGroup (p := p) (G := X ⧸ Q)).to_le hrange
  have hker2 : IsPGroup 2 f.ker := by
    rw [hker]
    exact hQ2.comap_subtype
  refine hθ.2.2.2.1 K hKn ?_ ?_
  ·
    have : Group.IsSolvable f.ker := by
      have : Group.IsNilpotent f.ker := hker2.isNilpotent
      infer_instance
    have : Group.IsSolvable f.range := by
      have : Group.IsNilpotent f.range := hrp.isNilpotent
      infer_instance
    exact Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict (by
      intro x hx
      exact ⟨⟨x, (MonoidHom.mem_ker).mpr (by simpa using congrArg Subtype.val hx)⟩, rfl⟩)
  ·
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
    obtain ⟨a, ha⟩ := hrp.exists_card_eq
    obtain ⟨b, hb⟩ := hker2.exists_card_eq
    rw [h1, ha, hb]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp
        (Nat.prime_three.dvd_of_dvd_pow h)
      exact hp3 this.symm
    · have := Nat.prime_three.dvd_of_dvd_pow h
      omega

theorem map_inf_normalizer_eq_top {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) {X P : Subgroup G}
    (hchar : ∃ R : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p R ((Sec4.oTwoP p ↥X).map X.subtype) ∧ P ≤ R ∧
        (P.subgroupOf R).Characteristic) :
    ((X ⊓ Subgroup.normalizer (P : Set G)).subgroupOf X).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ := by
  obtain ⟨R, ⟨Q', hQ'⟩, hPR, hPc⟩ := hchar
  have hOn : (Sec4.oTwoP p ↥X).Normal := Subgroup.Normal.comap (CFSG.pCore_normal (p := p)) _
  let e : ↥(Sec4.oTwoP p ↥X) ≃* ↥((Sec4.oTwoP p ↥X).map X.subtype) :=
    (Sec4.oTwoP p ↥X).equivMapOfInjective X.subtype X.subtype_injective
  let Q : Sylow p ↥(Sec4.oTwoP p ↥X) :=
    Q'.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcomp : (X.subtype.comp (Sec4.oTwoP p ↥X).subtype).comp e.symm.toMonoidHom =
      ((Sec4.oTwoP p ↥X).map X.subtype).subtype := by
    ext k
    exact congrArg Subtype.val (e.apply_symm_apply k)
  have hQR : ((Q : Subgroup ↥(Sec4.oTwoP p ↥X)).map (Sec4.oTwoP p ↥X).subtype).map X.subtype =
      R := by
    have hQc : (Q : Subgroup ↥(Sec4.oTwoP p ↥X)) =
        (Q' : Subgroup ↥((Sec4.oTwoP p ↥X).map X.subtype)).map e.symm.toMonoidHom :=
      Sylow.coe_mapSurjective _ _
    rw [hQc, Subgroup.map_map, Subgroup.map_map, hcomp, hQ']
  have hF := Sylow.normalizer_sup_eq_top Q
  rw [eq_top_iff]
  rintro q -
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hx : x ∈ Subgroup.normalizer
      ((Q : Subgroup ↥(Sec4.oTwoP p ↥X)).map (Sec4.oTwoP p ↥X).subtype : Set ↥X) ⊔
        Sec4.oTwoP p ↥X :=
    hF ▸ Subgroup.mem_top x
  obtain ⟨n, hn, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  have hnR : (n : G) ∈ Subgroup.normalizer (R : Set G) := by
    rw [← hQR]
    exact Subgroup.le_normalizer_map X.subtype ⟨n, hn, rfl⟩
  have hNRP : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (P : Set G) := by
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := R)
      (P.subgroupOf R)
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPR] at h
  refine ⟨n, Subgroup.mem_subgroupOf.mpr ⟨n.2, hNRP hnR⟩, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hoθ : o ∈ aschbacherSolvableCore 3 ↥X := oTwoP_le_theta hp3 ↥X ho
  simpa using hoθ

theorem mem_thetaQuotCentralizer_of_mem {A X : Subgroup G} {e : G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (he : e ∈ Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype)) :
    e ∈ Sec4.thetaQuotCentralizer X := by
  set θX := inSubgroup (aschbacherSolvableCore 3) X with hθX
  have hXθ : X ≤ Subgroup.normalizer (θX : Set G) := Sec6.le_normalizer_theta X
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hAX he.1, fun l hl => ?_⟩
  have h1 := he.2 l hl
  have h2 := (Subgroup.mem_normalizer_iff.mp (hXθ (inv_mem hl)) _).mp h1
  have he' : l⁻¹ * (e * l * e⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (e * l * e⁻¹) := by group
  rw [he'] at h2
  exact h2

theorem mem_thetaQuotCentralizer_of_dData {A X : Subgroup G} {c' : G} {L' : Subgroup G} {d : G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hd : DData152 A X c' L' d) :
    c' ∈ Sec4.thetaQuotCentralizer X := by
  refine mem_thetaQuotCentralizer_of_mem hAX ?_
  have hsc := hd.cent
  have hc : c' ∈ (Subgroup.closure {c', d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  rw [← hsc] at hc
  exact hc

theorem inf_centralizer_le_frattini_or_le_of
    {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y M X : Subgroup G} {c' : G} {p : ℕ} {P : Subgroup G} (hctx : Ctx152 A LB Y M X)
    (hcA : c' ∈ A) (hc3 : c' ^ 3 = 1) (hcC : c' ∈ Sec4.thetaQuotCentralizer X)
    (hP : PData152 A X p P) (hp3 : p ≠ 3) :
    P ⊓ Subgroup.centralizer ({c'} : Set G) ≤ (frattini ↥P).map P.subtype ∨
      P ≤ Subgroup.centralizer ({c'} : Set G) := by
  have : Fact p.Prime := ⟨hP.prime⟩
  have hp : p.Prime := hP.prime
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  obtain ⟨hXs, hX60⟩ := Proof152Gen.isSimpleGroup_theta_quot_of_ctx152 hctx
  have hXq := isQuasisimple_theta_of_mem_thetaComponentsIn hctx.mem_comp
  have h2 : 2 ∣ Nat.card (↥X ⧸ θ) := by rw [hX60]; norm_num
  have hPp : IsPGroup p P := by
    rcases hP.type_p with ⟨-, h⟩ | ⟨-, h⟩
    · exact IsPGroup.of_card h
    · exact IsPGroup.of_card h
  have hV := card_frattini_quot_eq hP.type_p
  set W := X ⊓ Subgroup.normalizer (P : Set G) with hW
  have hWcov := map_inf_normalizer_eq_top hp3 hP.char_p
  have hcW : c' ∈ Subgroup.normalizer (W : Set G) := by
    have hcX : Subgroup.zpowers c' ≤ Subgroup.normalizer (X : Set G) :=
      Subgroup.zpowers_le.mpr (hctx.norm_x hcA)
    have hcP : Subgroup.zpowers c' ≤
        Subgroup.normalizer ((Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr (Sec6.normalizer_le_normalizer_normalizer P (hP.norm_p hcA))
    exact Late.le_normalizer_inf hcX hcP (Subgroup.mem_zpowers c')
  have hNcov := Proof152Gen.map_inf_centralizer_eq_top (inf_le_left : W ≤ X) hcW hc3 hcC hWcov
  set Nc := W ⊓ Subgroup.centralizer ({c'} : Set G) with hNc
  have hNcU : Nc ≤ Subgroup.normalizer ((P ⊓ Subgroup.centralizer ({c'} : Set G) :
      Subgroup G) : Set G) :=
    Late.le_normalizer_inf (inf_le_left.trans inf_le_right)
      (inf_le_right.trans (Subgroup.le_normalizer))
  have hC : ∀ (x : G) (hx : x ∈ X), x ∈ Subgroup.centralizer (P : Set G) →
      (⟨x, hx⟩ : ↥X) ∈ θ := by
    intro x hx hxc
    obtain ⟨y, hy, hyx⟩ := oTwoOddIn_le_theta hXs h2 (hP.cent_p ⟨hx, hxc⟩)
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    exact this ▸ hy
  set U := P ⊓ Subgroup.centralizer ({c'} : Set G) with hU
  set ℓ := (U.subgroupOf P).map (QuotientGroup.mk' (frattini ↥P)) with hℓ
  have hℓdvd : Nat.card ℓ ∣ p ^ 2 := hV ▸ Subgroup.card_subgroup_dvd_card ℓ
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).mp hℓdvd
  interval_cases k
  ·
    left
    have hbot : ℓ = ⊥ := Subgroup.eq_bot_of_card_eq ℓ (by rw [hk, pow_zero])
    rw [hℓ, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    intro x hx
    exact ⟨⟨x, hx.1⟩, hbot (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  ·
    exfalso
    exact Proof152Flag.false_of_invariant_line hP.odd hPp hV θ hXq.1 h2
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) hNcov hC hNcU
      (by rw [hk, pow_one])
  ·
    right
    have htop : ℓ = ⊤ := Subgroup.eq_top_of_card_eq ℓ (by rw [hk, hV])
    have hsup : U.subgroupOf P ⊔ frattini ↥P = ⊤ := by
      have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' (frattini ↥P)) (U.subgroupOf P)
      rw [← hℓ, htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have hUtop : U.subgroupOf P = ⊤ := frattini_nongenerating hsup
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥P) ∈ U.subgroupOf P := hUtop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp h1).2

theorem inf_centralizer_le_frattini_or_le
    {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y M X : Subgroup G} {c' : G} {L' : Subgroup G} {d : G} {p : ℕ} {P : Subgroup G}
    (hA : Late.IsE27 A) (hpt : Pt152 A LB Y M X c' L') (hd : DData152 A X c' L' d)
    (hP : PData152 A X p P) (hp3 : p ≠ 3) :
    P ⊓ Subgroup.centralizer ({c'} : Set G) ≤ (frattini ↥P).map P.subtype ∨
      P ≤ Subgroup.centralizer ({c'} : Set G) := by
  have hcA : c' ∈ A := (zpowers_mem_omegaA_iff.mp hpt.omega).1
  exact inf_centralizer_le_frattini_or_le_of hpt.ctx hcA (hA.1.2 c' hcA)
    (mem_thetaQuotCentralizer_of_dData hpt.ctx.norm_x hd) hP hp3

end Proof152F

variable {G : Type} [Group G] [Finite G]

@[expose] def Step152ConfFC (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (d : G) (p : ℕ) (P T K S : Subgroup G),
    Pt152 A LB Y M X c' L' → DData152 A X c' L' d → PData152 A X p P →
    TData152 A LB X P T → KData152 A LB P T K S →
    P ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype →
    ((P ⊔ CFSG.Open.pCoreOf 2 K).subgroupOf K).Normal →
    ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G) →
    generalizedFitting ↥(P ⊔ S) = CFSG.pCore 2 ↥(P ⊔ S) →
      ¬ P ≤ Subgroup.centralizer ({c'} : Set G)

@[expose] noncomputable def Step152ConfFCR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfFC A (lB A)

theorem ne_three_of_le_theta {A X : Subgroup G} {p : ℕ} {P K : Subgroup G}
    (hP : PData152 A X p P) (hθ : P ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype) : p ≠ 3 := by
  rintro rfl
  have hθ3 := (solvable_prime_complement_core_characterization (H := ↥K)
    Nat.prime_three).2.2.1
  obtain ⟨n, hn, hPn⟩ : ∃ n : ℕ, 2 ≤ n ∧ Nat.card P = 3 ^ n := by
    rcases hP.type_p with ⟨-, h⟩ | ⟨-, h⟩
    · exact ⟨2, le_rfl, h⟩
    · exact ⟨3, by norm_num, h⟩
  have hdvd : Nat.card P ∣ Nat.card (aschbacherSolvableCore 3 ↥K) := by
    have h := Subgroup.card_dvd_of_le hθ
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at h
  rw [hPn] at hdvd
  exact hθ3 ((dvd_pow_self 3 (by omega : n ≠ 0)).trans hdvd)

theorem step152ConfF_of
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (hFC : Step152ConfFC A (lB A)) : Step152ConfF A (lB A) := by
  intro Y M X c' L' d p P T K S hpt hd hP hT hK hθ hn hps hfs
  rcases Proof152F.inf_centralizer_le_frattini_or_le h.isE27 hpt hd hP
      (ne_three_of_le_theta hP hθ) with hfr | hPc
  · exact hfr
  · exact absurd hPc (hFC Y M X c' L' d p P T K S hpt hd hP hT hK hθ hn hps hfs)

theorem step152ConfFR_of
    (hFC : Step152ConfFCR) : Step152ConfFR :=
  fun G _ _ A c L hR => step152ConfF_of hR.toSec14Std (hFC G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
