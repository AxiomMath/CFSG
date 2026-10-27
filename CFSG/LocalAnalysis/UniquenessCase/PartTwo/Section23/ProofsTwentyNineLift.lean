module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KBorelFixed
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem bar2_comap_map_subgroupOf {K S : Subgroup G}
    (hO : CFSG.Open.pCoreOf 2 K ≤ S) :
    Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
        (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (S.subgroupOf K)) =
      S.subgroupOf K := by
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hO' : CFSG.pCore 2 ↥K ≤ S.subgroupOf K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hO (Subgroup.mem_map_of_mem K.subtype hx)
  change Subgroup.comap q (Subgroup.map q (S.subgroupOf K)) = S.subgroupOf K
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hO']

theorem rhoL_apply_mk {K : Subgroup G} {r : G}
    (hr : r ∈ Subgroup.normalizer (K : Set G)) (x : ↥K) :
    UC6S846.rhoL K ⟨r, hr⟩ (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥K)
        ⟨r * (x : G) * r⁻¹, (Subgroup.mem_normalizer_iff.mp hr x).mp x.2⟩ := by
  rw [QuotientGroup.mk'_apply, UC6S846.rhoL_mk, QuotientGroup.mk'_apply]
  congr 1

private theorem rhoL_map_sbar {K S R : Subgroup G}
    (hRS : R ≤ Subgroup.normalizer (S : Set G)) {r : G}
    (hrK : r ∈ Subgroup.normalizer (K : Set G)) (hrR : r ∈ R) :
    Subgroup.map (UC6S846.rhoL K ⟨r, hrK⟩).toMonoidHom
        (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (S.subgroupOf K)) =
      Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (S.subgroupOf K) := by
  classical
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let Sbar : Subgroup (Bar2 K) := (S.subgroupOf K).map q
  change Subgroup.map (UC6S846.rhoL K ⟨r, hrK⟩).toMonoidHom Sbar = Sbar
  have hle : Subgroup.map (UC6S846.rhoL K ⟨r, hrK⟩).toMonoidHom Sbar ≤ Sbar := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    change UC6S846.rhoL K ⟨r, hrK⟩ (q s) ∈ Sbar
    rw [rhoL_apply_mk]
    refine Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr ?_)
    exact (Subgroup.mem_normalizer_iff.mp (hRS hrR) (s : G)).mp
      (Subgroup.mem_subgroupOf.mp hs)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  exact le_of_eq (Subgroup.card_map_of_injective (K := Sbar)
    (f := (UC6S846.rhoL K ⟨r, hrK⟩).toMonoidHom)
    (UC6S846.rhoL K ⟨r, hrK⟩).injective).symm

theorem rhoL_mul_inv_mem_of_mem_sup {K S R : Subgroup G}
    {H : Subgroup (Bar2 K)}
    (hRS : R ≤ Subgroup.normalizer (S : Set G))
    (hHnorm : H ≤ Subgroup.normalizer
      ((Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (S.subgroupOf K) :
        Subgroup (Bar2 K)) : Set (Bar2 K)))
    (hcent : ∀ r (hr : r ∈ Subgroup.normalizer (K : Set G)), r ∈ R →
      ∀ h ∈ H, UC6S846.rhoL K ⟨r, hr⟩ h * h⁻¹ ∈
        Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (S.subgroupOf K))
    {r : G} (hrK : r ∈ Subgroup.normalizer (K : Set G)) (hrR : r ∈ R)
    {x : ↥K}
    (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥K) x ∈
      H ⊔ Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (S.subgroupOf K)) :
    UC6S846.rhoL K ⟨r, hrK⟩ (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x)⁻¹ ∈
      Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (S.subgroupOf K) := by
  classical
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let Sbar : Subgroup (Bar2 K) := (S.subgroupOf K).map q
  let rho := UC6S846.rhoL K ⟨r, hrK⟩
  change rho (q x) * (q x)⁻¹ ∈ Sbar
  have hmap : Subgroup.map rho.toMonoidHom Sbar = Sbar := rhoL_map_sbar hRS hrK hrR
  have hdecomp : q x ∈ (H : Set (Bar2 K)) * (Sbar : Set (Bar2 K)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right H Sbar hHnorm]
    exact hx
  obtain ⟨h, hhH, s, hsS, hhs⟩ := hdecomp
  have hrho : rho (q x) * (q x)⁻¹ =
      (rho h * h⁻¹) * (h * (rho s * s⁻¹) * h⁻¹) := by
    rw [← hhs]
    simp only [map_mul, mul_inv_rev]
    group
  rw [hrho]
  refine Sbar.mul_mem (hcent r hrK hrR h hhH) ?_
  have hrhos : rho s ∈ Sbar := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem rho.toMonoidHom hsS
  have hb : rho s * s⁻¹ ∈ Sbar := Sbar.mul_mem hrhos (Sbar.inv_mem hsS)
  exact (Subgroup.mem_normalizer_iff.mp (hHnorm hhH) (rho s * s⁻¹)).mp hb

theorem mem_normalizer_of_bar2_mem {K S : Subgroup G} (hSK : S ≤ K)
    (hcomap : Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (S.subgroupOf K)) = S.subgroupOf K)
    {x : ↥K}
    (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥K) x ∈
      Subgroup.normalizer ((Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
        (S.subgroupOf K) : Subgroup (Bar2 K)) : Set (Bar2 K))) :
    (x : G) ∈ Subgroup.normalizer (S : Set G) := by
  classical
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let Sbar : Subgroup (Bar2 K) := (S.subgroupOf K).map q
  change q x ∈ Subgroup.normalizer (Sbar : Set (Bar2 K)) at hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    change (x : G) * y * (x : G)⁻¹ ∈ S
    let yK : ↥K := ⟨y, hSK hy⟩
    have hybar : q yK ∈ Sbar :=
      Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr hy)
    have hconj : q (x * yK * x⁻¹) ∈ Sbar := by
      have h := (Subgroup.mem_normalizer_iff.mp hx yK).mp hybar
      simpa [q, map_mul, map_inv] using h
    have hmemK : x * yK * x⁻¹ ∈ S.subgroupOf K := by
      rw [← hcomap, Subgroup.mem_comap]
      exact hconj
    simpa [yK] using Subgroup.mem_subgroupOf.mp hmemK
  · exact le_of_eq (Subgroup.card_map_of_injective (K := S)
      (f := (MulAut.conj (x : G)).toMonoidHom) (MulAut.conj (x : G)).injective).symm

theorem commutator_mem_of_rhoL {K S : Subgroup G}
    (hcomap : Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (S.subgroupOf K)) = S.subgroupOf K)
    {r x : G} (hr : r ∈ Subgroup.normalizer (K : Set G)) (hx : x ∈ K)
    (h : UC6S846.rhoL K ⟨r, hr⟩ (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x, hx⟩) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x, hx⟩)⁻¹ ∈
      Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (S.subgroupOf K)) :
    r * x * r⁻¹ * x⁻¹ ∈ S := by
  classical
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let Sbar : Subgroup (Bar2 K) := (S.subgroupOf K).map q
  let xK : ↥K := ⟨x, hx⟩
  have hrxK : r * x * r⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hr x).mp hx
  have hcommK : r * x * r⁻¹ * x⁻¹ ∈ K := K.mul_mem hrxK (K.inv_mem hx)
  have hq : q ⟨r * x * r⁻¹ * x⁻¹, hcommK⟩ =
      UC6S846.rhoL K ⟨r, hr⟩ (q xK) * (q xK)⁻¹ := by
    rw [rhoL_apply_mk, ← map_inv, ← map_mul]
    congr 1
  have hmemK : (⟨r * x * r⁻¹ * x⁻¹, hcommK⟩ : ↥K) ∈ S.subgroupOf K := by
    rw [← hcomap, Subgroup.mem_comap]
    rw [hq]
    exact h
  simpa using Subgroup.mem_subgroupOf.mp hmemK

private theorem exists_complement_equiv_of_coprime {P : Type} [Group P] [Finite P]
    {N : Subgroup P} [N.Normal] (hcop : Nat.Coprime (Nat.card N) N.index)
    {H : Type} [Group H] (e : P ⧸ N ≃* H) :
    ∃ A : Subgroup P, A.IsComplement' N ∧ Nonempty (A ≃* H) := by
  obtain ⟨A, hA⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hAcomm : A.IsComplement' N := Subgroup.isComplement'_comm.mp hA
  refine ⟨A, hAcomm, ?_⟩
  exact ⟨hAcomm.QuotientMulEquiv.symm.trans e⟩

private theorem mod_sylow_disjoint {K S : Subgroup G} (hS2 : IsPGroup 2 S)
    {H : Subgroup (Bar2 K)} (hHodd : Odd (Nat.card H)) :
    Disjoint H (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (S.subgroupOf K)) := by
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let Sbar : Subgroup (Bar2 K) := (S.subgroupOf K).map q
  rw [disjoint_iff]
  refine Subgroup.inf_eq_bot_of_coprime ?_
  obtain ⟨n, hn⟩ := (hS2.comap_subtype (K := K)).map q |>.exists_card_eq
  have hn' : Nat.card Sbar = 2 ^ n := by simpa [Sbar] using hn
  rw [hn']
  exact Nat.Coprime.pow_right n hHodd.coprime_two_right

private theorem mod_sylow_normal_and_quotient {K S : Subgroup G}
    (hO : CFSG.Open.pCoreOf 2 K ≤ S) {H : Subgroup (Bar2 K)}
    (hHnorm : H ≤ Subgroup.normalizer
      ((Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (S.subgroupOf K) :
        Subgroup (Bar2 K)) : Set (Bar2 K)))
    (hHdisj : Disjoint H
      (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (S.subgroupOf K)))
    (P : Subgroup ↥K)
    (hP : P = (H ⊔ Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      (S.subgroupOf K)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))
    (N : Subgroup P)
    (hN : N = (S.subgroupOf K).subgroupOf P) :
    ∃ (hNnormal : N.Normal), Nonempty (letI := hNnormal; P ⧸ N ≃* H) := by
  subst P
  subst N
  classical
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let Sbar : Subgroup (Bar2 K) := (S.subgroupOf K).map q
  let Pbar : Subgroup (Bar2 K) := H ⊔ Sbar
  let P : Subgroup ↥K := Pbar.comap q
  let N : Subgroup P := (S.subgroupOf K).subgroupOf P
  have hcomap : Subgroup.comap q Sbar = S.subgroupOf K := bar2_comap_map_subgroupOf hO
  have hPbar_le_N : Pbar ≤ Subgroup.normalizer (Sbar : Set (Bar2 K)) :=
    sup_le hHnorm Subgroup.le_normalizer
  haveI hSbar_normal : (Sbar.subgroupOf Pbar).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hPbar_le_N
  have hHsub : Sbar.subgroupOf H = ⊥ :=
    Subgroup.subgroupOf_eq_bot.mpr hHdisj.symm
  let f : P →* ↥Pbar := q.subgroupComap Pbar
  let g : P →* (↥Pbar) ⧸ (Sbar.subgroupOf Pbar) :=
    (QuotientGroup.mk' (Sbar.subgroupOf Pbar)).comp f
  have hg_surj : Function.Surjective g :=
    (QuotientGroup.mk'_surjective (Sbar.subgroupOf Pbar)).comp
      (MonoidHom.subgroupComap_surjective_of_surjective q Pbar
        (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K)))
  have hker : g.ker = N := by
    ext x
    change (f x : (↥Pbar) ⧸ (Sbar.subgroupOf Pbar)) = 1 ↔ x ∈ N
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    change q (x : ↥K) ∈ Sbar ↔ (x : ↥K) ∈ S.subgroupOf K
    rw [← hcomap, Subgroup.mem_comap]
  have hNnormal : N.Normal := hker ▸ (inferInstance : g.ker.Normal)
  let ePS : P ⧸ N ≃* (↥Pbar) ⧸ (Sbar.subgroupOf Pbar) :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg_surj)
  have hSbar_normal_H : (Sbar.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hHnorm
  let eH : (↥Pbar) ⧸ (Sbar.subgroupOf Pbar) ≃* ↥H :=
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient H Sbar hHnorm).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hHsub).trans QuotientGroup.quotientBot)
  exact ⟨hNnormal, ⟨ePS.trans eH⟩⟩

private theorem mod_sylow_card {K S : Subgroup G} (hSK : S ≤ K) {H : Subgroup (Bar2 K)}
    (P : Subgroup ↥K)
    (hP : P = (H ⊔ Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      (S.subgroupOf K)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))
    (N : Subgroup P)
    (hN : N = (S.subgroupOf K).subgroupOf P) :
    Nat.card N = Nat.card S := by
  subst P
  subst N
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let Sbar : Subgroup (Bar2 K) := (S.subgroupOf K).map q
  let N : Subgroup ((H ⊔ Sbar).comap q) :=
    (S.subgroupOf K).subgroupOf ((H ⊔ Sbar).comap q)
  change Nat.card N = Nat.card S
  have hSP : S.subgroupOf K ≤ (H ⊔ Sbar).comap q := by
    intro x hx
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_sup_right (Subgroup.mem_map_of_mem q hx)
  calc Nat.card N = Nat.card (S.subgroupOf K) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv
    _ = Nat.card S := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv

private theorem mod_sylow_coprime {P : Type} [Group P] [Finite P] {N : Subgroup P}
    {K S : Subgroup G} (hS2 : IsPGroup 2 S) {H : Subgroup (Bar2 K)}
    (hHodd : Odd (Nat.card H))
    (hNcard : Nat.card N = Nat.card S) (hNindex : N.index = Nat.card H) :
    Nat.Coprime (Nat.card N) N.index := by
  rw [hNcard, hNindex]
  obtain ⟨n, hn⟩ := hS2.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_left n hHodd.coprime_two_left

theorem exists_borelLift_of_mod_sylow {K S R : Subgroup G}
    (hSK : S ≤ K) (hS2 : IsPGroup 2 S) (hO : CFSG.Open.pCoreOf 2 K ≤ S)
    (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hRS : R ≤ Subgroup.normalizer (S : Set G))
    {H : Subgroup (Bar2 K)}
    (hHnorm : H ≤ Subgroup.normalizer
      ((Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (S.subgroupOf K) :
        Subgroup (Bar2 K)) : Set (Bar2 K)))
    (hHodd : Odd (Nat.card H))
    (hcent : ∀ r (hr : r ∈ Subgroup.normalizer (K : Set G)), r ∈ R →
      ∀ h ∈ H, UC6S846.rhoL K ⟨r, hr⟩ h * h⁻¹ ∈
        Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (S.subgroupOf K)) :
    ∃ A : Subgroup G, A ≤ K ⊓ Subgroup.normalizer (S : Set G) ∧
      Nonempty (A ≃* H) ∧
      ∀ r ∈ R, ∀ a ∈ A, r * a * r⁻¹ * a⁻¹ ∈ S := by
  classical
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let Sbar : Subgroup (Bar2 K) := (S.subgroupOf K).map q
  let Pbar : Subgroup (Bar2 K) := H ⊔ Sbar
  let P : Subgroup ↥K := Pbar.comap q
  let N : Subgroup P := (S.subgroupOf K).subgroupOf P
  have hcomap : Subgroup.comap q Sbar = S.subgroupOf K := bar2_comap_map_subgroupOf hO
  have hPbar_le_N : Pbar ≤ Subgroup.normalizer (Sbar : Set (Bar2 K)) :=
    sup_le hHnorm Subgroup.le_normalizer
  have hHdisj : Disjoint H Sbar := mod_sylow_disjoint hS2 hHodd
  obtain ⟨hNnormal, ⟨ePN⟩⟩ :=
    mod_sylow_normal_and_quotient hO hHnorm hHdisj P rfl N rfl
  haveI := hNnormal
  have hNcard : Nat.card N = Nat.card S := mod_sylow_card hSK P rfl N rfl
  have hNindex : N.index = Nat.card H := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr ePN.toEquiv
  have hcop : Nat.Coprime (Nat.card N) N.index :=
    mod_sylow_coprime hS2 hHodd hNcard hNindex
  obtain ⟨A, -, ⟨eAH⟩⟩ := exists_complement_equiv_of_coprime hcop ePN
  let AG : Subgroup G := A.map (K.subtype.comp P.subtype)
  have hAG_le_K : AG ≤ K := by
    rintro _ ⟨a, -, rfl⟩
    exact (a : P).1.2
  have hAG_le_NS : AG ≤ Subgroup.normalizer (S : Set G) := by
    rintro _ ⟨a, -, rfl⟩
    exact mem_normalizer_of_bar2_mem hSK hcomap (hPbar_le_N a.2)
  have hcomm : ∀ r ∈ R, ∀ a ∈ AG, r * a * r⁻¹ * a⁻¹ ∈ S := by
    intro r hrR a ha
    obtain ⟨aP, -, rfl⟩ := Subgroup.mem_map.mp ha
    have hrK : r ∈ Subgroup.normalizer (K : Set G) := hRK hrR
    exact commutator_mem_of_rhoL hcomap hrK aP.1.2
      (rhoL_mul_inv_mem_of_mem_sup hRS hHnorm hcent hrK hrR aP.2)
  refine ⟨AG, le_inf hAG_le_K hAG_le_NS, ⟨?_, hcomm⟩⟩
  exact ⟨(Subgroup.equivMapOfInjective A (K.subtype.comp P.subtype)
    (K.subtype_injective.comp P.subtype_injective)).symm.trans eAH⟩

theorem pCoreOf_le_inf_sylow {D : Data G} {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) :
    CFSG.Open.pCoreOf 2 K ≤ D.T ⊓ K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hpc : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal (p := 2) (G := ↥K)
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hK.1
  have hMN : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKn
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K :=
    D.sylowM.inf_of_le_normalizer hKM hMN
  obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
  have hle : CFSG.pCore 2 ↥K ≤ (Q : Subgroup ↥K) :=
    IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) Q
  calc CFSG.Open.pCoreOf 2 K = Subgroup.map K.subtype (CFSG.pCore 2 ↥K) := rfl
    _ ≤ Subgroup.map K.subtype (Q : Subgroup ↥K) := Subgroup.map_mono hle
    _ = D.T ⊓ K := by
        rw [hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSyl.le]

theorem T_le_normalizer_of_normal {D : Data G} {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) :
    D.T ≤ Subgroup.normalizer (K : Set G) := by
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hK.1
  exact D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKn)

theorem T_le_normalizer_inf {D : Data G} {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) :
    D.T ≤ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G) := by
  intro t ht
  have htT : Subgroup.map (MulAut.conj t).toMonoidHom D.T = D.T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ht)
  have htK : Subgroup.map (MulAut.conj t).toMonoidHom K = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (T_le_normalizer_of_normal hK hKn ht)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective]
  change Subgroup.map (MulAut.conj t).toMonoidHom D.T ⊓
      Subgroup.map (MulAut.conj t).toMonoidHom K = D.T ⊓ K
  rw [htT, htK]

theorem sylowImage_isSylow {D : Data G} {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) :
    ∃ S : Sylow 2 (Bar2 K),
      (S : Subgroup (Bar2 K)) = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
        ((D.T ⊓ K).subgroupOf K) := by
  classical
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hK.1
  have hMN : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKn
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K :=
    D.sylowM.inf_of_le_normalizer hKM hMN
  obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
  let S : Sylow 2 (Bar2 K) :=
    Sylow.mapSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      (QuotientGroup.mk'_surjective _) Q
  refine ⟨S, ?_⟩
  rw [Sylow.coe_mapSurjective, hQ]

theorem theta_isPGroup {D : Data G} (K : Subgroup G) {R : Subgroup G} (hR : R ≤ D.T) :
    IsPGroup 2 ((R.subgroupOf (Subgroup.normalizer (K : Set G))).map
      (UC6S846.rhoL K)) :=
  ((D.sylowM.isPGroup.to_le hR).comap_subtype
      (K := Subgroup.normalizer (K : Set G))).map (UC6S846.rhoL K)

theorem theta_maps_sylow {D : Data G} {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) {R : Subgroup G}
    (hR : R ≤ D.T) {S : Sylow 2 (Bar2 K)}
    (hS : (S : Subgroup (Bar2 K)) = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      ((D.T ⊓ K).subgroupOf K)) :
    ∀ θ ∈ (R.subgroupOf (Subgroup.normalizer (K : Set G))).map (UC6S846.rhoL K),
      ∀ x ∈ (S : Subgroup (Bar2 K)), θ x ∈ (S : Subgroup (Bar2 K)) := by
  intro θ hθ x hx
  obtain ⟨r, hr, hθeq⟩ := Subgroup.mem_map.mp hθ
  have hrT : (r : G) ∈ D.T := hR (Subgroup.mem_subgroupOf.mp hr)
  have hmap : Subgroup.map (UC6S846.rhoL K ⟨(r : G), r.2⟩).toMonoidHom
      (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
        ((D.T ⊓ K).subgroupOf K)) =
      Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
        ((D.T ⊓ K).subgroupOf K) :=
    rhoL_map_sbar (T_le_normalizer_inf hK hKn) r.2 hrT
  rw [hS] at hx ⊢
  rw [← hθeq]
  rw [← hmap]
  exact Subgroup.mem_map_of_mem (UC6S846.rhoL K ⟨(r : G), r.2⟩).toMonoidHom hx

private theorem exists_borelLift_of_bar2OddData (D : Data G) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    {S : Sylow 2 (Bar2 K)}
    (hS : (S : Subgroup (Bar2 K)) = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      ((D.T ⊓ K).subgroupOf K))
    {H : Subgroup (Bar2 K)}
    (hHnorm : H ≤ Subgroup.normalizer ((S : Subgroup (Bar2 K)) : Set (Bar2 K)))
    (hHodd : Odd (Nat.card H))
    (hcent : ∀ θ ∈ (D.T.subgroupOf (Subgroup.normalizer (K : Set G))).map (UC6S846.rhoL K),
      ∀ h ∈ H, θ h * h⁻¹ ∈ (S : Subgroup (Bar2 K))) :
    ∃ A : Subgroup G, A ≤ K ⊓ Subgroup.normalizer (D.T : Set G) ∧
      Nonempty (A ≃* H) ∧
      ∀ r ∈ D.T, ∀ a ∈ A, r * a * r⁻¹ * a⁻¹ ∈ D.T ⊓ K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT_le_NK : D.T ≤ Subgroup.normalizer (K : Set G) :=
    T_le_normalizer_of_normal hK hKn
  have hT_le_NS : D.T ≤ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G) :=
    T_le_normalizer_inf hK hKn
  have hO : CFSG.Open.pCoreOf 2 K ≤ D.T ⊓ K := pCoreOf_le_inf_sylow hK hKn
  have hT2 : IsPGroup 2 D.T := CFSG.ABGLocalTools.IsSylowOf.isPGroup D.sylowM
  have hS2 : IsPGroup 2 ↥(D.T ⊓ K) :=
    IsPGroup.to_inf_left (p := 2) (H := D.T) (K := K) hT2
  have hHnorm' : H ≤ Subgroup.normalizer
      ((Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ((D.T ⊓ K).subgroupOf K) :
        Subgroup (Bar2 K)) : Set (Bar2 K)) := by
    rwa [hS] at hHnorm
  have hcent' : ∀ r (hr : r ∈ Subgroup.normalizer (K : Set G)), r ∈ D.T →
      ∀ h ∈ H, UC6S846.rhoL K ⟨r, hr⟩ h * h⁻¹ ∈
        Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ((D.T ⊓ K).subgroupOf K) := by
    intro r hr hrT h hh
    have hθ : UC6S846.rhoL K ⟨r, hr⟩ ∈
        (D.T.subgroupOf (Subgroup.normalizer (K : Set G))).map (UC6S846.rhoL K) :=
      Subgroup.mem_map_of_mem (UC6S846.rhoL K) (Subgroup.mem_subgroupOf.mpr hrT)
    have hfix := hcent _ hθ h hh
    rwa [hS] at hfix
  obtain ⟨A, hA, ⟨eAH⟩, hcomm⟩ :=
    exists_borelLift_of_mod_sylow inf_le_right hS2 hO hT_le_NK hT_le_NS
      hHnorm' hHodd hcent'
  have hA_le_NT : A ≤ Subgroup.normalizer (D.T : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left, Subgroup.commutator_le]
    intro r hr a ha
    rw [commutatorElement_def]
    exact (hcomm r hr a ha).1
  exact ⟨A, le_inf (hA.trans inf_le_left) hA_le_NT, ⟨eAH⟩, hcomm⟩

theorem exists_borelLift_of_isL2 (D : Data G) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKn : (K.subgroupOf D.M).Normal) {k : ℕ} (hX : IsL2 (Bar2 K) k) :
    ∃ e m : ℕ, k = 2 ^ e * m ∧ ∃ A : Subgroup G,
      A ≤ K ⊓ Subgroup.normalizer (D.T : Set G) ∧ IsCyclic A ∧
      Nat.card A = 2 ^ m - 1 ∧
      (m = 1 → 2 ≤ k → ∃ t : G, ∃ ht : t ∈ Subgroup.normalizer (K : Set G),
        t ∈ D.T ∧ ∀ x : Bar2 K, UC6S846.rhoL K ⟨t, ht⟩ ^ (k / 2) ≠ MulAut.conj x) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := sylowImage_isSylow hK hKn
  let Θ : Subgroup (MulAut (Bar2 K)) :=
    (D.T.subgroupOf (Subgroup.normalizer (K : Set G))).map (UC6S846.rhoL K)
  have hΘ : IsPGroup 2 Θ := theta_isPGroup K le_rfl
  have hΘS : ∀ θ ∈ Θ, ∀ x ∈ (S : Subgroup (Bar2 K)), θ x ∈ (S : Subgroup (Bar2 K)) :=
    theta_maps_sylow hK hKn le_rfl hS
  obtain ⟨e, m, hk, H, hHcyc, hHcard, hHnorm, hHcent, hHnot⟩ :=
    exists_borelFixed_of_isL2 hX Θ hΘ S hΘS
  have hk1 : 1 ≤ k := hX.admissible.2.1
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0, mul_zero] at hk
      omega
    · exact hmpos
  have hHodd : Odd (Nat.card H) := by
    rw [hHcard]
    exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  obtain ⟨A, hA, ⟨eAH⟩, -⟩ :=
    exists_borelLift_of_bar2OddData D hK hKn hS hHnorm hHodd hHcent
  refine ⟨e, m, hk, A, hA, (MulEquiv.isCyclic eAH).mpr hHcyc,
    (Nat.card_congr eAH.toEquiv).trans hHcard, ?_⟩
  intro hm hk2
  obtain ⟨θ, hθ, hnot⟩ := hHnot hm hk2
  obtain ⟨r, hr, hθeq⟩ := Subgroup.mem_map.mp hθ
  refine ⟨(r : G), r.2, Subgroup.mem_subgroupOf.mp hr, ?_⟩
  rw [← hθeq] at hnot
  simpa using hnot

theorem exists_borelLift_of_isSz (hAut : KSzTwoAut) (D : Data G) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) {k : ℕ}
    (hX : IsSz (Bar2 K) k) :
    ∃ A : Subgroup G, A ≤ K ⊓ Subgroup.normalizer (D.T : Set G) ∧
      Nat.card A = 2 ^ k - 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := sylowImage_isSylow hK hKn
  let Θ : Subgroup (MulAut (Bar2 K)) :=
    (D.T.subgroupOf (Subgroup.normalizer (K : Set G))).map (UC6S846.rhoL K)
  have hΘ : IsPGroup 2 Θ := theta_isPGroup K le_rfl
  have hΘS : ∀ θ ∈ Θ, ∀ x ∈ (S : Subgroup (Bar2 K)), θ x ∈ (S : Subgroup (Bar2 K)) :=
    theta_maps_sylow hK hKn le_rfl hS
  obtain ⟨H, hHcard, hHnorm, hHcent⟩ :=
    exists_borelFixed_of_isSz hAut hX Θ hΘ S hΘS
  have hk1 : 1 ≤ k := hX.admissible.2.1
  have hHodd : Odd (Nat.card H) := by
    rw [hHcard]
    exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  obtain ⟨A, hA, ⟨eAH⟩, -⟩ :=
    exists_borelLift_of_bar2OddData D hK hKn hS hHnorm hHodd hHcent
  exact ⟨A, hA, (Nat.card_congr eAH.toEquiv).trans hHcard⟩

theorem exists_borelLift_of_isJ1 (D : Data G) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKn : (K.subgroupOf D.M).Normal) (hX : IsJ1 (Bar2 K)) :
    ∃ A : Subgroup G, A ≤ K ⊓ Subgroup.normalizer (D.T : Set G) ∧
      Odd (Nat.card A) ∧ ¬ IsMulCommutative A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := sylowImage_isSylow hK hKn
  let Θ : Subgroup (MulAut (Bar2 K)) :=
    (D.T.subgroupOf (Subgroup.normalizer (K : Set G))).map (UC6S846.rhoL K)
  have hΘ : IsPGroup 2 Θ := theta_isPGroup K le_rfl
  have hΘS : ∀ θ ∈ Θ, ∀ x ∈ (S : Subgroup (Bar2 K)), θ x ∈ (S : Subgroup (Bar2 K)) :=
    theta_maps_sylow hK hKn le_rfl hS
  obtain ⟨H, hHodd, hHnoncomm, hHnorm, hHcent⟩ :=
    exists_borelFixed_of_isJ1 hX Θ hΘ S hΘS
  obtain ⟨A, hA, ⟨eAH⟩, -⟩ :=
    exists_borelLift_of_bar2OddData D hK hKn hS hHnorm hHodd hHcent
  refine ⟨A, hA, ?_, ?_⟩
  · rw [Nat.card_congr eAH.toEquiv]
    exact hHodd
  · intro hAcomm
    apply hHnoncomm
    refine IsMulCommutative.mk ⟨fun x y => ?_⟩
    have h := hAcomm.is_comm.comm (eAH.symm x) (eAH.symm y)
    simpa using congrArg eAH h

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
