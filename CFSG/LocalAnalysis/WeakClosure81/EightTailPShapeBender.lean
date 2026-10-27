module

public import CFSG.Quasithin.Background.OddCentralKerSylowTI
public import CFSG.LocalAnalysis.WeakClosure81.TwelveSubgroup
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitSmall
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenL2
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfPSU
public import CFSG.CGT.Timmesfeld75.ListWCSzU3
public import CFSG.GroupTheory.CardMapInfKer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.GH74.Uniqueness.Bender

private theorem wc85bd_odd_card_center {X : Type} [Group X] [Finite X]
    (hp : CFSG.pCore 2 X = ⊥) : Odd (Nat.card (Subgroup.center X)) :=
  CFSG.CGT.Timmesfeld75.odd_card_center fun N hN h2 =>
    le_bot_iff.mp (by simpa [hp] using CFSG.LieType.BorelTits.le_pCore 2 hN h2)

private theorem wc85bd_sylowTwoTI_of_benderType
    {K : Type} [Group K] [Finite K] {n i e : ℕ} (h : BenderType K n i e) : SylowTwoTI K := by
  intro P Q hPQ
  obtain ⟨t, hc⟩ := h.exists_benderCore P
  by_contra hne
  exact hPQ (hc.sylow_eq_of_ne_bot hne inf_le_left inf_le_right).symm

private theorem wc85bd_benderType_of_isSzGp {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : IsSzGp Y n) : BenderType Y n 2 1 :=
  rankOne_benderType_sz h

private theorem wc85bd_benderType_of_isPSUGp {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : IsPSUGp Y 3 n) :
    BenderType Y n 3 ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) := by
  obtain ⟨-, hn1, -, hne⟩ := CFSG.Blueprint.LieModel.admissible h
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · have hn1' : n = 1 := by omega
      exact absurd (by rw [hn1']; norm_num : ((3 : ℕ), 2 ^ n) = (3, 2)) hne
    · exact hge
  have hcl : StatedClassicalModel Y .PSU 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  obtain ⟨e⟩ := CFSG.CGT.Timmesfeld75.exists_psu3_of_statedClassicalModel hn2 hcl
  exact BenderType.unitary n hn2 (e.trans (MulEquiv.subgroupCongr
    (show CFSG.Open.PSU3 2 n = CFSG.Theory.Comparator.PSU3Model n from rfl)))

private theorem wc85bd_unitary_transvection_sq {m n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) {x : StatedProj (StatedSU m (2 ^ n) F)}
    (hx : IsUnitaryTransvectionIn m n x) : x * x = 1 := by
  obtain ⟨g, hg, hr⟩ := hx
  have hgg : g * g = 1 :=
    CFSG.LocalAnalysis.WeakClosure81.statedSU_mul_self_of_rank_one hF g hr
  let φ : ↥(StatedSU m (2 ^ n) F) →* StatedProj (StatedSU m (2 ^ n) F) :=
    QuotientGroup.mk' ((StatedScalars (Fin m) F).subgroupOf (StatedSU m (2 ^ n) F))
  have hgφ : φ g = x := hg
  rw [← hgφ]
  change φ g * φ g = 1
  rw [← map_mul, hgg, map_one]

private theorem wc85bd_card_sylow_eq {Y : Type} [Group Y] [Finite Y] {n m : ℕ}
    (hY : Nat.card Y = 2 ^ n * m) (hm : Odd m) (S : Sylow 2 Y) :
    Nat.card (S : Subgroup Y) = 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hidx : Odd (S : Subgroup Y).index :=
    Nat.not_even_iff_odd.mp fun h => S.not_dvd_index (even_iff_two_dvd.mp h)
  have hmain : 2 ^ k * (S : Subgroup Y).index = 2 ^ n * m := by
    rw [← hk, Subgroup.card_mul_index, hY]
  have hle : k ≤ n := by
    have hdvd : 2 ^ k ∣ 2 ^ n * m :=
      hmain ▸ dvd_mul_right (2 ^ k) (S : Subgroup Y).index
    have hcop : Nat.Coprime (2 ^ k) m := (Nat.coprime_two_left.mpr hm).pow_left k
    exact (Nat.pow_dvd_pow_iff_le_right (show 1 < 2 by norm_num)).mp
      (hcop.dvd_of_dvd_mul_right hdvd)
  have hge : n ≤ k := by
    have hdvd : 2 ^ n ∣ 2 ^ k * (S : Subgroup Y).index :=
      hmain ▸ dvd_mul_right (2 ^ n) m
    have hcop : Nat.Coprime (2 ^ n) (S : Subgroup Y).index :=
      (Nat.coprime_two_left.mpr hidx).pow_left n
    exact (Nat.pow_dvd_pow_iff_le_right (show 1 < 2 by norm_num)).mp
      (hcop.dvd_of_dvd_mul_right hdvd)
  rw [hk, Nat.le_antisymm hle hge]

private theorem wc85bd_rootCenter_conj {K : Type} [Group K] (P : Subgroup K) (g : K) :
    conjSubgroup (rootCenter P) g = rootCenter (conjSubgroup P g) := by
  rw [conjSubgroup, conjSubgroup, rootCenter_map]

private theorem wc85bd_conjSubgroup_ne_bot {X : Type} [Group X] {S : Subgroup X} {g : X}
    (hS : S ≠ ⊥) : conjSubgroup S g ≠ ⊥ := by
  intro hbot
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS
  have hmem : g⁻¹ * (x : X) * g ∈ conjSubgroup S g := by
    rw [mem_conjSubgroup_iff]
    have hx : g * (g⁻¹ * (x : X) * g) * g⁻¹ = (x : X) := by group
    rw [hx]
    exact x.2
  rw [hbot, Subgroup.mem_bot] at hmem
  apply hx1
  apply Subtype.ext
  calc (x : X) = g * (g⁻¹ * (x : X) * g) * g⁻¹ := by group
    _ = 1 := by rw [hmem]; group

theorem exists_sylow_weaklyClosed_of_bender_root {X : Type}
    [Group X] [Finite X] {n : ℕ} {S : Subgroup X} (hp : CFSG.pCore 2 X = ⊥)
    (h : (∃ m : ℕ, m ≤ 3 ∧ IsSpGp (X ⧸ Subgroup.center X) m n ∧ IsSymplecticRootGroup X m n S) ∨
      (IsPSUGp (X ⧸ Subgroup.center X) 3 n ∧ IsUnitaryRootGroup X 3 n S) ∨
      (IsSzGp (X ⧸ Subgroup.center X) n ∧ IsSuzukiRootGroup X S)) :
    ∃ P : Sylow 2 X, S ≤ (P : Subgroup X) ∧ IsWeaklyClosedIn S (P : Subgroup X) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (Subgroup.center X)) := wc85bd_odd_card_center hp
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.center X := QuotientGroup.ker_mk' _
  by_cases hSb : S = ⊥
  · refine ⟨default, ?_, ?_⟩
    · rw [hSb]; exact bot_le
    · intro g hg
      rw [hSb] at hg ⊢
      rw [conjSubgroup, Subgroup.map_bot]
  · rcases h with ⟨m, hm3, hSp, hroot⟩ | ⟨hPSU, hroot⟩ | ⟨hSz, hroot⟩
    ·
      obtain ⟨hScard, k, hk, F, hFld, hFin, hFcard, e, htrans⟩ := hroot
      have hk1 : k = 1 := by
        rcases k with _ | k'
        · exfalso
          obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSb
          have hw := htrans (w : X) w.2 (fun h => hw1 (Subtype.ext h))
          simp only [IsSymplecticTransvectionIn] at hw
          haveI : Subsingleton (Matrix (Fin 0 ⊕ Fin 0) (Fin 0 ⊕ Fin 0) F) :=
            ⟨fun a b => by ext i j; exact Sum.elim Fin.elim0 Fin.elim0 i⟩
          have hsub : (((e (QuotientGroup.mk w) : ↥(StatedSp 0 F)) :
              GL (Fin 0 ⊕ Fin 0) F) : Matrix (Fin 0 ⊕ Fin 0) (Fin 0 ⊕ Fin 0) F) - 1 = 0 :=
            Subsingleton.elim _ _
          rw [hsub, Matrix.rank_zero] at hw
          exact one_ne_zero hw.symm
        · omega
      have hm2 : m = 2 := by omega
      have hSp2 : IsSpGp (X ⧸ Subgroup.center X) 2 n := hm2 ▸ hSp
      have hn1 : 1 ≤ n := by
        by_contra hlt
        have hn0 : n = 0 := by omega
        rw [hn0, pow_zero] at hScard
        exact hSb (Subgroup.eq_bot_of_card_eq S hScard)
      have hL2 : IsL2Gp (X ⧸ Subgroup.center X) n := isL2Gp_of_isSpGp_two hSp2
      have hcardY : Nat.card (X ⧸ Subgroup.center X) = 2 ^ n * (4 ^ n - 1) :=
        card_eq_of_isL2Gp hL2
      have hoddY : Odd (4 ^ n - 1) :=
        Nat.Even.sub_odd (Nat.one_le_pow n 4 (by norm_num))
          (Even.pow_of_ne_zero (show Even 4 by decide) (by omega)) odd_one
      have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := n) hScard
      obtain ⟨P, hSP⟩ := hS2.exists_le_sylow
      let Pbar : Sylow 2 (X ⧸ Subgroup.center X) := P.mapSurjective hπ
      have hPbar_coe : (Pbar : Subgroup (X ⧸ Subgroup.center X)) = (P : Subgroup X).map π :=
        Sylow.coe_mapSurjective hπ P
      have hSylCard : Nat.card (Pbar : Subgroup (X ⧸ Subgroup.center X)) = 2 ^ n :=
        wc85bd_card_sylow_eq hcardY hoddY Pbar
      have hPinf : (P : Subgroup X) ⊓ Subgroup.center X = ⊥ :=
        CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd P.isPGroup' hodd
      have hPcard : Nat.card (P : Subgroup X) = 2 ^ n := by
        have h1 : Nat.card ((P : Subgroup X).map π) = Nat.card (P : Subgroup X) :=
          CFSG.card_map_eq_card_of_inf_ker_eq_bot π (by rw [hker]; exact hPinf)
        rw [← h1, ← hPbar_coe, hSylCard]
      have hSPeq : S = (P : Subgroup X) :=
        Subgroup.eq_of_le_of_card_ge hSP (le_of_eq (by rw [hPcard, hScard]))
      refine ⟨P, hSP, ?_⟩
      rw [hSPeq]
      intro g hg
      refine Subgroup.eq_of_le_of_card_ge hg ?_
      rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    ·
      obtain ⟨hScard, F, hFld, hFin, hFcard, e, htrans⟩ := hroot
      letI : Field F := hFld
      letI : Finite F := hFin
      have hB : BenderType (X ⧸ Subgroup.center X) n 3
          ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) := wc85bd_benderType_of_isPSUGp hPSU
      have hTIY : SylowTwoTI (X ⧸ Subgroup.center X) :=
        wc85bd_sylowTwoTI_of_benderType hB
      have hTIX : SylowTwoTI X :=
        SylowTwoTI.of_central_odd_ker π hπ (by rw [hker])
          (by rw [hker]; exact hodd) hTIY
      have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := n) hScard
      obtain ⟨P, hSP⟩ := hS2.exists_le_sylow
      let Pbar : Sylow 2 (X ⧸ Subgroup.center X) := P.mapSurjective hπ
      have hPbar_coe : (Pbar : Subgroup (X ⧸ Subgroup.center X)) = (P : Subgroup X).map π :=
        Sylow.coe_mapSurjective hπ P
      obtain ⟨t, hc⟩ := hB.exists_benderCore Pbar
      have hPinf : (P : Subgroup X) ⊓ Subgroup.center X = ⊥ :=
        CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd P.isPGroup' hodd
      have hSinf : S ⊓ Subgroup.center X = ⊥ :=
        CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hS2 hodd
      have hSle : S ≤ rootCenter (P : Subgroup X) := by
        intro s hs
        rw [rootCenter, Subgroup.mem_inf]
        refine ⟨hSP hs, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro p hp
        by_cases hs1 : s = 1
        · subst hs1; simp
        · have hπs_mem : π s ∈ (Pbar : Subgroup (X ⧸ Subgroup.center X)) := by
            rw [hPbar_coe]
            exact Subgroup.mem_map_of_mem π (hSP hs)
          have hπs_ne : π s ≠ 1 := by
            intro h1
            have hsk : s ∈ π.ker := by rw [MonoidHom.mem_ker]; exact h1
            rw [hker] at hsk
            have : s ∈ S ⊓ Subgroup.center X := ⟨hs, hsk⟩
            rw [hSinf, Subgroup.mem_bot] at this
            exact hs1 this
          have hπs_sq : π s * π s = 1 := by
            have htrans' : IsUnitaryTransvectionIn 3 n (e (π s)) := htrans s hs hs1
            have h := wc85bd_unitary_transvection_sq hFcard htrans'
            exact e.injective (by rw [map_mul, h, map_one])
          have horder : orderOf (π s) = 2 := orderOf_eq_prime (by rwa [pow_two]) hπs_ne
          have hπs_root : π s ∈ rootCenter (Pbar : Subgroup (X ⧸ Subgroup.center X)) :=
            hc.center_of_involution (π s) (Subgroup.le_normalizer hπs_mem) horder
          have hcz := (Subgroup.mem_centralizer_iff.mp
            (Subgroup.mem_inf.mp hπs_root).2) (π p) (Subgroup.mem_map_of_mem π hp)
          have hkerp : p * s * (s * p)⁻¹ ∈ π.ker := by
            rw [MonoidHom.mem_ker]
            calc π (p * s * (s * p)⁻¹) = π p * π s * (π s * π p)⁻¹ := by
                  simp [map_mul, map_inv]
              _ = 1 := by rw [hcz, mul_inv_cancel]
          have hmem : p * s * (s * p)⁻¹ ∈ (P : Subgroup X) ⊓ Subgroup.center X :=
            ⟨P.mul_mem (P.mul_mem hp (hSP hs)) (P.inv_mem (P.mul_mem (hSP hs) hp)),
              by rwa [← hker]⟩
          rw [hPinf, Subgroup.mem_bot] at hmem
          exact mul_inv_eq_one.mp hmem
      have hrootmap_le :
          (rootCenter (P : Subgroup X)).map π ≤
            rootCenter (Pbar : Subgroup (X ⧸ Subgroup.center X)) := by
        rintro y ⟨x, hx, rfl⟩
        rw [rootCenter, Subgroup.mem_inf]
        refine ⟨?_, ?_⟩
        · rw [hPbar_coe]
          exact Subgroup.mem_map_of_mem π ((rootCenter_le (P : Subgroup X)) hx)
        · rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [hPbar_coe] at hz
          obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hz
          have hcx := (Subgroup.mem_centralizer_iff.mp hx.2) q hq
          rw [← map_mul, ← map_mul, hcx]
      have hrootmap_ge :
          rootCenter (Pbar : Subgroup (X ⧸ Subgroup.center X)) ≤
            (rootCenter (P : Subgroup X)).map π := by
        intro y hy
        have hyP : y ∈ (Pbar : Subgroup (X ⧸ Subgroup.center X)) :=
          (Subgroup.mem_inf.mp hy).1
        rw [hPbar_coe] at hyP
        obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hyP
        refine Subgroup.mem_map.mpr ⟨p, ?_, rfl⟩
        rw [rootCenter, Subgroup.mem_inf]
        refine ⟨hp, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        have hcy := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2) (π q)
          (Subgroup.mem_map_of_mem π hq)
        have hkerq : q * p * (p * q)⁻¹ ∈ π.ker := by
          rw [MonoidHom.mem_ker]
          calc π (q * p * (p * q)⁻¹) = π q * π p * (π p * π q)⁻¹ := by
                simp [map_mul, map_inv]
            _ = 1 := by rw [hcy, mul_inv_cancel]
        have hmem : q * p * (p * q)⁻¹ ∈ (P : Subgroup X) ⊓ Subgroup.center X :=
          ⟨P.mul_mem (P.mul_mem hq hp) (P.inv_mem (P.mul_mem hp hq)),
            by rwa [← hker]⟩
        rw [hPinf, Subgroup.mem_bot] at hmem
        exact mul_inv_eq_one.mp hmem
      have hrootmap : (rootCenter (P : Subgroup X)).map π =
          rootCenter (Pbar : Subgroup (X ⧸ Subgroup.center X)) :=
        le_antisymm hrootmap_le hrootmap_ge
      have hkerbot : rootCenter (P : Subgroup X) ⊓ π.ker = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_inf] at hx
        rw [hker] at hx
        have hmem : x ∈ (P : Subgroup X) ⊓ Subgroup.center X :=
          ⟨(rootCenter_le (P : Subgroup X)) hx.1, hx.2⟩
        rwa [hPinf, Subgroup.mem_bot] at hmem
      have hRootCard : Nat.card (rootCenter (P : Subgroup X)) = 2 ^ n := by
        have h1 : Nat.card ((rootCenter (P : Subgroup X)).map π) =
            Nat.card (rootCenter (P : Subgroup X)) :=
          CFSG.card_map_eq_card_of_inf_ker_eq_bot π hkerbot
        rw [← h1, hrootmap, hc.card_center]
      have hS_eq : S = rootCenter (P : Subgroup X) :=
        Subgroup.eq_of_le_of_card_ge hSle (le_of_eq (by rw [hRootCard, hScard]))
      refine ⟨P, hSP, ?_⟩
      intro g hg
      let P' : Sylow 2 X := g⁻¹ • P
      have hP'coe : (P' : Subgroup X) = conjSubgroup (P : Subgroup X) g := by
        rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
        simp only [conjSubgroup]
        exact congrArg (fun f : X →* X => (P : Subgroup X).map f) (by ext x; rfl)
      have hSg_nb : conjSubgroup S g ≠ ⊥ := wc85bd_conjSubgroup_ne_bot hSb
      have hint : (P : Subgroup X) ⊓ (P' : Subgroup X) ≠ ⊥ := by
        intro hbot
        apply hSg_nb
        have hle : conjSubgroup S g ≤ (P : Subgroup X) ⊓ (P' : Subgroup X) := by
          refine le_inf hg ?_
          rw [hP'coe]
          exact Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hSP
        rw [hbot] at hle
        exact le_bot_iff.mp hle
      have hP'P : P' = P := by
        by_contra hne
        exact hint (hTIX P P' (fun h => hne h.symm))
      have hPg : conjSubgroup (P : Subgroup X) g = (P : Subgroup X) := by
        rw [← hP'coe, hP'P]
      calc conjSubgroup S g = conjSubgroup (rootCenter (P : Subgroup X)) g := by rw [hS_eq]
        _ = rootCenter (conjSubgroup (P : Subgroup X) g) := wc85bd_rootCenter_conj P g
        _ = rootCenter (P : Subgroup X) := by rw [hPg]
        _ = S := hS_eq.symm
    ·
      obtain ⟨T, hT⟩ := hroot
      have hST : S ≤ (T : Subgroup X) := fun x hx => ((hT x).1 hx).1
      have hS_eq : S = rootCenter (T : Subgroup X) := by
        ext x
        constructor
        · intro hx
          obtain ⟨hxT, hxc⟩ := (hT x).1 hx
          exact ⟨hxT, fun y hy => (hxc y hy).symm⟩
        · intro hx
          obtain ⟨hxT, hxc⟩ := hx
          exact (hT x).2 ⟨hxT, fun y hy => (hxc y hy).symm⟩
      have hB : BenderType (X ⧸ Subgroup.center X) n 2 1 := wc85bd_benderType_of_isSzGp hSz
      have hTIY : SylowTwoTI (X ⧸ Subgroup.center X) :=
        wc85bd_sylowTwoTI_of_benderType hB
      have hTIX : SylowTwoTI X :=
        SylowTwoTI.of_central_odd_ker π hπ (by rw [hker])
          (by rw [hker]; exact hodd) hTIY
      refine ⟨T, hST, ?_⟩
      intro g hg
      let T' : Sylow 2 X := g⁻¹ • T
      have hT'coe : (T' : Subgroup X) = conjSubgroup (T : Subgroup X) g := by
        rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
        simp only [conjSubgroup]
        exact congrArg (fun f : X →* X => (T : Subgroup X).map f) (by ext x; rfl)
      have hSg_nb : conjSubgroup S g ≠ ⊥ := wc85bd_conjSubgroup_ne_bot hSb
      have hint : (T : Subgroup X) ⊓ (T' : Subgroup X) ≠ ⊥ := by
        intro hbot
        apply hSg_nb
        have hle : conjSubgroup S g ≤ (T : Subgroup X) ⊓ (T' : Subgroup X) := by
          refine le_inf hg ?_
          rw [hT'coe]
          exact Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hST
        rw [hbot] at hle
        exact le_bot_iff.mp hle
      have hT'T : T' = T := by
        by_contra hne
        exact hint (hTIX T T' (fun h => hne h.symm))
      have hTg : conjSubgroup (T : Subgroup X) g = (T : Subgroup X) := by
        rw [← hT'coe, hT'T]
      calc conjSubgroup S g = conjSubgroup (rootCenter (T : Subgroup X)) g := by rw [hS_eq]
        _ = rootCenter (conjSubgroup (T : Subgroup X) g) := wc85bd_rootCenter_conj T g
        _ = rootCenter (T : Subgroup X) := by rw [hTg]
        _ = S := hS_eq.symm

end CFSG.LocalAnalysis.WeakClosure81

end
