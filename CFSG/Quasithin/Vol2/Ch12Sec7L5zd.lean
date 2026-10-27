module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zb
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zc
public import CFSG.Quasithin.Vol2.Ch1A3Cat

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.ASInputs S127 S127.L715 S127.L716
  G31
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}
  (s : Set714 G T L V t z)
include s

theorem cCompSpan_eq
    (h1222 : Stmt12_2_2) (h39 : A39ForSQTK) :
    cCompSpan (⊤ : Subgroup ↥(H714 T L V z)) = perfectCore (⊤ : Subgroup ↥(H714 T L V z)) := by
  have hy := s.setting.hyp.hyp
  have hspan0 := CFSG.Quasithin.lemma_1_2_1_one hy.qtke hy.simple hy.nonabelian h39
    (s.pCoreOf_H_ne_bot h1222)
  have h1 : perfectCore (⊤ : Subgroup ↥(H714 T L V z)) =
      (perfectCore (H714 T L V z)).subgroupOf (H714 T L V z) := by
    rw [← C124.perfectCore_subgroupOf' (le_refl (H714 T L V z)), Subgroup.subgroupOf_self]
  rw [h1, ← hspan0, cCompSpan_eq_map_subtype (H714 T L V z), Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]

theorem exists_cComp_top
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) :
    ∃ L' ∈ cComp (⊤ : Subgroup ↥(H714 T L V z)), L'.map (s.rho h1222) = ⊤ := by
  have hV : ∀ v : ↥(Ut T L V z), v ^ 2 = 1 := fun v =>
    Subtype.ext ((s.elemAbelian_Ut h1222).2 _ v.2)
  let _ : Module (ZMod 2) (Additive ↥(Ut T L V z)) :=
    AddCommGroup.zmodModule (n := 2) (two_nsmul_eq_zero hV)
  obtain ⟨n, hn, Δ, h0, hM⟩ := s.exists_mulHyp h1222 hU
  rw [← s.range_rho h1222] at hM
  have h2 := s.card_le_two h1222 h37 h38 h39 hM hn
  obtain ⟨k, hk⟩ := s.odd_card h1222 hM h0
  have hi : ∀ i : Fin n, i = ⟨0, hn⟩ := fun i => Fin.ext (by have := i.2; omega)
  have hΔ : Δ ⟨0, hn⟩ = orbitOn (s.rho h1222).range (X1 T L V z) := by
    rw [← hM.union]
    ext Y
    simp only [Set.mem_iUnion]
    exact ⟨fun h => ⟨_, h⟩, fun ⟨i, h⟩ => hi i ▸ h⟩
  have htop : g31V (Δ ⟨0, hn⟩) = ⊤ := by
    rw [hΔ]
    exact s.g31V_eq_top h1222
  have hG : g31G (s.rho h1222).range (Δ ⟨0, hn⟩) = ⊤ := by
    rw [eq_top_iff]
    intro ψ _
    have hψ : ψ ∈ g31Stab (g31V (Δ ⟨0, hn⟩)) := fun v => by
      simp only [htop, Subgroup.mem_top]
    obtain ⟨g, hg, hgv⟩ := hM.autAll ⟨0, hn⟩ (g31Restr (g31V (Δ ⟨0, hn⟩)) ⟨ψ, hψ⟩)
    have hgψ : g = ψ := MulEquiv.ext fun v => by
      have := hgv ⟨v, htop ▸ Subgroup.mem_top v⟩
      simpa [g31Restr_apply] using this
    rw [← hgψ]
    exact hg
  obtain ⟨L', hL', hLeq⟩ := hM.exists_cComp_map_eq (s.cCompSpan_eq h1222 h39) ⟨0, hn⟩
  exact ⟨L', hL', hLeq.trans hG⟩

theorem pCore_le_ker_rho
    (h1222 : Stmt12_2_2) : CFSG.pCore 2 ↥(H714 T L V z) ≤ (s.rho h1222).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := s.rho h1222 with hρ
  set M := (CFSG.pCore 2 ↥(H714 T L V z)).map ρ with hM
  have hMR : M ≤ ρ.range := Subgroup.map_le_range _ _
  have hMN : ρ.range ≤ Subgroup.normalizer (M : Set (MulAut ↥(Ut T L V z))) := by
    rintro _ ⟨h, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨h * x * h⁻¹, CFSG.pCore_normal.conj_mem x hx h, by simp [map_mul, map_inv]⟩
    · rintro ⟨x, hx, hxm⟩
      refine ⟨h⁻¹ * x * h, ?_, ?_⟩
      · have := CFSG.pCore_normal.conj_mem x hx h⁻¹
        simpa using this
      · have e : m = (ρ h)⁻¹ * ρ x * ρ h := by
          rw [hxm]
          group
        simp only [map_mul, map_inv, e]
  have hMp : IsPGroup 2 ↥M := CFSG.pCore_isPGroup.map ρ
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hMR hMN hMp
  rw [hρ, s.range_rho h1222, s.pCoreOf_Hs h1222, le_bot_iff, hM, Subgroup.map_eq_bot_iff] at hle
  exact hle

@[expose] noncomputable def rhoBar
    (h1222 : Stmt12_2_2) :
    (↥(H714 T L V z) ⧸ CFSG.pCore 2 ↥(H714 T L V z)) →* MulAut ↥(Ut T L V z) :=
  QuotientGroup.lift _ (s.rho h1222) (s.pCore_le_ker_rho h1222)

theorem rhoBar_mk
    (h1222 : Stmt12_2_2) (h : ↥(H714 T L V z)) :
    s.rhoBar h1222 (QuotientGroup.mk' _ h) = s.rho h1222 h := rfl

omit s in
theorem lift3_pair {W : Type} [CommGroup W] [Finite W] {Y : Fin 2 → MulAut W}
    (hY3 : ∀ i, Y i ^ 3 = 1) (hcard : 3 ^ 2 ≤ Nat.card ↥(Subgroup.closure (Set.range Y))) :
    Y 0 ≠ 1 ∧ Y 1 ∉ Subgroup.zpowers (Y 0) := by
  have hle : ∀ i, (∀ j, Y j ∈ Subgroup.zpowers (Y i)) → False := by
    intro i h
    have h1 : Subgroup.closure (Set.range Y) ≤ Subgroup.zpowers (Y i) :=
      (Subgroup.closure_le _).2 (by rintro _ ⟨j, rfl⟩; exact h j)
    have h2 := Subgroup.card_le_of_le h1
    rw [Nat.card_zpowers] at h2
    have h3 : orderOf (Y i) ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hY3 i))
    omega
  refine ⟨fun h0 => hle 1 fun j => ?_, fun h1 => hle 0 fun j => ?_⟩
  · fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, h0]
      exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · fin_cases j
    · exact Subgroup.mem_zpowers _
    · exact h1

theorem dim_le_five
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2)
    (h36 : CFSG.QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V)
    {d : ℕ} (hd : Nat.card ↥(Ut T L V z) = 2 ^ d) : d ≤ 5 := by
  by_contra hd6
  push Not at hd6
  have hy := s.setting.hyp.hyp
  have hH := s.pCoreOf_H_ne_bot h1222
  have hV : ∀ v : ↥(Ut T L V z), v ^ 2 = 1 := fun v =>
    Subtype.ext ((s.elemAbelian_Ut h1222).2 _ v.2)
  obtain ⟨L', hL', hLtop⟩ := s.exists_cComp_top h1222 h37 h38 h39 hU
  set X : Subgroup (↥(H714 T L V z) ⧸ CFSG.pCore 2 ↥(H714 T L V z)) :=
    L'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥(H714 T L V z))) with hX
  have hXc : X ∈ cComp (⊤ : Subgroup (↥(H714 T L V z) ⧸ CFSG.pCore 2 ↥(H714 T L V z))) := by
    have h := modO2Image_mem_cComp (map_subtype_mem_cComp hL')
    have e : modO2Image (H714 T L V z) (L'.map (H714 T L V z).subtype) = X := by
      rw [modO2Image, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective (H714 T L V z).subtype_injective]
    rwa [e] at h
  set π : ↥X →* MulAut ↥(Ut T L V z) := (s.rhoBar h1222).comp X.subtype with hπdef
  have hπ : Function.Surjective π := by
    intro ψ
    have hψ : ψ ∈ L'.map (s.rho h1222) := by rw [hLtop]; exact Subgroup.mem_top ψ
    obtain ⟨l, hl, rfl⟩ := hψ
    exact ⟨⟨QuotientGroup.mk' _ l, Subgroup.mem_map_of_mem _ hl⟩, rfl⟩
  have hQ := CFSG.Quasithin.sqtkHyp_quotient_of_pCoreOf_ne_bot hy.qtke hy.simple hy.nonabelian hH
  have hcore := h36 _ hQ.toCat X hXc
  obtain ⟨Y, Tau, hY3, hYc, -, -, hcard⟩ := Lift3.exists_mulAut hV hd (k := 2) (by omega)
  obtain ⟨ha1, hba⟩ := lift3_pair hY3 hcard
  have hnot := Lift3.not_threeRankLeOne π hπ (hY3 0) (hY3 1) (hYc 0 1) ha1 hba
  have hq : CFSG.IsQuasisimple ↥X := by
    rcases hcore.1 with hcomp | h3 | h4
    · exact hcomp.1
    · exact absurd (Lift3.threeRankLeOne_of_case3' h3) hnot
    · exact absurd (Lift3.threeRankLeOne_of_case4' h4) hnot
  have hker : ∀ c ∈ π.ker, ∀ g : ↥X, c * g = g * c := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (MonoidHom.normal_ker π) with h | h
    · exfalso
      obtain ⟨x, hx⟩ := hπ (Y 0)
      have : x ∈ π.ker := h ▸ Subgroup.mem_top x
      rw [MonoidHom.mem_ker, hx] at this
      exact ha1 this
    · intro c hc g
      exact (Subgroup.mem_center_iff.mp (h hc) g).symm
  have h3 := Lift3.le_pRank_of_surjective hV hd (k := 3) (by omega) π hπ hker
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN3 : ¬ 3 ∣ Nat.card ↥(CFSG.pCore 2 ↥(H714 T L V z)) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥(H714 T L V z)))
    rw [hm]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have e1 := CFSG.Quasithin.pRank_top_subtype (p := 3) X
  have e2 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (le_top : X ≤ ⊤)
  have e3 := CFSG.SectionRank.pRank_quotient_eq (p := 3) (CFSG.pCore 2 ↥(H714 T L V z)) hN3
  have e4 := CFSG.Quasithin.pRank_top_subtype (p := 3) (H714 T L V z)
  have e5 := CFSG.Quasithin.pRank_le_two_of_pCoreOf_ne_bot hy.qtke hH Nat.prime_three
    (by norm_num)
  omega

end CFSG.Quasithin.H13.S127.L715.Set714
