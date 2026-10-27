module

public import CFSG.Quasithin.Background.SimsE213M
public import CFSG.Quasithin.Vol2.E2FourteenB
public import CFSG.Quasithin.Vol2.Ch3E215ME
public import CFSG.Quasithin.Vol2.Ch3E215MSp4

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace E215T

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem exists_orderOf_of_star {M X : Subgroup Γ} {c : E2.StarQuot M X} {d : ℕ}
    (hc : orderOf c = d) : ∃ x ∈ X, orderOf x = d := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  have hdvd : d ∣ orderOf y := hc ▸ orderOf_map_dvd (QuotientGroup.mk' _) y
  have hz : orderOf (y ^ (orderOf y / d)) = d := orderOf_pow_orderOf_div (orderOf_pos y).ne' hdvd
  exact ⟨((y ^ (orderOf y / d) : ↥X) : Γ), (y ^ (orderOf y / d)).2,
    by rw [Subgroup.orderOf_coe, hz]⟩

theorem relIndex_le_of_psl_or_sz {T M V I : Subgroup Γ} {g : Γ}
    (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hVZ : E2.star (M ⊓ I) I V ≤
      Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)))
    {k : ℕ} (hk : 2 ≤ k)
    (hY : IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) ∨ IsSz k (E2.StarQuot (M ⊓ I) I)) :
    (kerIn (M ⊓ I) I ⊓ V).relIndex V ≤ 2 ^ k := by
  have := E2P.finite_starQuot (M ⊓ I) I
  have hS := E2.isSylowTwoOf_star_inf (M := M) hsyl
  obtain ⟨hcard, -⟩ := E2.exists_conj_of_mem_center hk hY hS
  have hVT : E2.star (M ⊓ I) I V ≤ E2.star (M ⊓ I) I (T ⊓ I) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono I hp.le_T)
  rw [← SimsE210.natCard_star_eq_relIndex hp.V_le, ← hcard]
  exact Subgroup.card_le_of_le (le_inf hVT hVZ)

theorem e215DataOf_of_dih {T M V I : Subgroup Γ} {g : Γ} (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g)
    (hcharI : CharTwo I) (hIV : I ≠ V) {p a : ℕ} (hp' : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a)
    (e : E2.StarQuot (M ⊓ I) I ≃* DihedralGroup (p ^ a)) :
    Ch3E215M.E215DataOf I (M ⊓ I) V g := by
  have hcard : (kerIn (M ⊓ I) I).relIndex I = 2 * p ^ a := by
    rw [E2.relIndex_kerIn_eq_card, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  obtain ⟨x, hxI, hx⟩ := exists_orderOf_of_star (M := M ⊓ I) (X := I)
    (c := e.symm (DihedralGroup.r 1)) (by rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one])
  exact Ch3E215M.e215DataOf_of_dihedral hp hcharI hIV hp' hp2 ha hcard ⟨x, hxI, hx⟩

theorem e215DataOf_of_sz {T M V I : Subgroup Γ} {g : Γ}
    (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g) (hcharI : CharTwo I) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hVZ : E2.star (M ⊓ I) I V ≤
      Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)))
    {k : ℕ} (hY : IsSz k (E2.StarQuot (M ⊓ I) I)) : Ch3E215M.E215DataOf I (M ⊓ I) V g := by
  obtain ⟨hk3, hcardI⟩ := E2.card_of_isSz hY
  exact Ch3E215M.e215DataOf_of_sz hp hcharI hk3 ((E2.relIndex_kerIn_eq_card _ _).trans hcardI)
    (relIndex_le_of_psl_or_sz hp hsyl hVZ (by omega) (Or.inr hY))

theorem e215DataOf_of_psl
    {H T M V I : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V)
    (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g) (hcharI : CharTwo I) (hIV : I ≠ V)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) (hg : g ∈ I) (hgen : I = V ⊔ B6.conjSub g V)
    (hVZ : E2.star (M ⊓ I) I V ≤
      Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)))
    (hJ : pCoreOf 2 I = kerIn (M ⊓ I) I)
    (hBorel : E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I))) {k : ℕ} (hk : 2 ≤ k)
    (hY : IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I)) : Ch3E215M.E215DataOf I (M ⊓ I) V g := by
  by_cases hlt : (kerIn (M ⊓ I) I ⊓ V).relIndex V <
      (V ⊓ B6.conjSub g V).relIndex (kerIn (M ⊓ I) I ⊓ V)
  · exact Or.inl hlt
  refine Or.inr fun hMN => ?_
  have hTMI : T ⊓ I ≤ M ⊓ I := inf_le_inf_right I h.minParabolic.le
  obtain ⟨hP2, hVeq⟩ := E2.star_eq_center_of_psl_or_sz E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds hp hsyl hTMI hg hgen hVZ hMN hBorel hk (Or.inl hY)
  have hPJ := hP2.resolve_right (E2.not_isSz_three_of_isPSL hY)
  have hBor := E2.star_eq_normalizer_of_isBorelIn hTMI hsyl hBorel
  obtain ⟨s, hs, -, hsq⟩ := E2.exists_natural_of_psl hp hsyl hg hgen hMN hJ hPJ hBor hVeq hk hY
  have hVle := relIndex_le_of_psl_or_sz hp hsyl hVZ hk (Or.inl hY)
  have h2 := Ch3E215M.two_le_relIndex hp hcharI hIV
  have hq : 2 ≤ 2 ^ k := Nat.le_self_pow (by omega) 2
  have hs1 : s = 1 := by
    rcases Nat.lt_or_ge s 2 with hs2 | hs2
    · rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
      · rw [hs, pow_zero] at h2
        omega
      · rfl
    · exfalso
      have h3 : (2 ^ k) ^ 2 ≤ (2 ^ k) ^ s := Nat.pow_le_pow_right (by omega) hs2
      have h4 : 2 ^ k < (2 ^ k) ^ 2 := by nlinarith
      rw [← hs] at h3
      omega
  exact Ch3E215M.commutator_eq_bot_of_mul_self fun x hx => by
    rw [← pow_two]
    exact hsq hs1 x hx

theorem e215DataOf_of_sp4 {T M V I : Subgroup Γ} {g : Γ} (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g)
    (hcharI : CharTwo I) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hVZ : E2.star (M ⊓ I) I V ≤
      Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)))
    (hJ : pCoreOf 2 I = kerIn (M ⊓ I) I) {k : ℕ}
    (hY : IsSp4Full k (E2.StarQuot (M ⊓ I) I)) : Ch3E215M.E215DataOf I (M ⊓ I) V g := by
  have := E2P.finite_starQuot (M ⊓ I) I
  obtain ⟨K, _, _, _, hK, ⟨θ⟩⟩ := E213M.exists_antiSp_of_isSp4Full hY
  let ψ : ↥I →* CFSG.ComponentClassification.UnbalancedCatalog.SpChain.antiSp K :=
    θ.toMonoidHom.comp (E2P.starMap (M ⊓ I) I)
  have hψs : Function.Surjective ψ := θ.surjective.comp (E2P.starMap_surjective _ _)
  have hψk : ψ.ker = (kerIn (M ⊓ I) I).subgroupOf I := by
    ext x
    rw [MonoidHom.mem_ker, show ψ x = θ (E2P.starMap (M ⊓ I) I x) from rfl,
      MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, E2P.ker_starMap]
  have hJ2 : IsPGroup 2 ↥(kerIn (M ⊓ I) I) := by
    rw [← hJ]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I
  have hVT : E2.star (M ⊓ I) I V ≤ E2.star (M ⊓ I) I (T ⊓ I) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono I hp.le_T)
  have hV := E213M.card_le_of_le_centralizer hY (E2.isSylowTwoOf_star_inf (M := M) hsyl) hVT hVZ
  rw [SimsE210.natCard_star_eq_relIndex hp.V_le] at hV
  refine Ch3E215M.Sp4.e215DataOf_of_sp4 hp hcharI ψ hψs hψk hJ2 ?_
  rw [hK, ← pow_mul, Nat.mul_comm k 2]
  exact hV

end E215T

open E215T

theorem e215_two_OI :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V),
      CharTwo H → IsTISetIn V M →
      ∀ (I : Subgroup Γ) (g : Γ), IsInIHTV H T M V I → g ∈ I → I = V ⊔ conjSubgroup V g →
        ∀ A : Subgroup Γ, A = conjSubgroup V g ⊓ pCoreOf 2 I → rAV (autI h.elem A) < 2 := by
  intro Γ _ _ H T M V h hc hTI I g hI hg hIV A hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : conjSubgroup V g = B6.conjSub g⁻¹ V := SimsE210.conjSubgroup_eq_conjSub V g
  have hgen : I = V ⊔ B6.conjSub g⁻¹ V := e ▸ hIV
  have hg' : g⁻¹ ∈ I := I.inv_mem hg
  obtain ⟨hp, hVZ, -, -, hJ, -⟩ := RonanE211.e2_11C_all E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds h (E213M.noRoot_of_isInIHTV hI) hg' hgen
  have hcharI : CharTwo I := by
    have := E2.charTwo_of_charTwo h (hI.1 hg') hc
    rwa [← hgen] at this
  obtain ⟨hne, hrank⟩ := E213M.ne_and_rank h hI hp hcharI
  have hsyl : IsSylowTwoOf (T ⊓ I) I := hI.2.2.1
  have hdata : Ch3E215M.E215DataOf I (M ⊓ I) V g⁻¹ := by
    obtain ⟨-, -, -, -, k, -, hcase⟩ := hI
    rcases hcase with ⟨hk1, hY | hY, hBorel⟩ | ⟨-, p, a, hp', hp2, ha, ⟨d⟩⟩ |
        ⟨-, -, hY, -, -, -⟩
    · exact e215DataOf_of_psl h hp hcharI hne hsyl hg' hgen hVZ hJ hBorel (by omega) hY
    · exact e215DataOf_of_sz hp hcharI hsyl hVZ hY
    · exact e215DataOf_of_dih hp hcharI hne hp' hp2 ha d
    · exact e215DataOf_of_sp4 hp hcharI hsyl hVZ hJ hY
  have hcount := Ch3E215M.count_lt_of_e215DataOf hp hcharI hne hrank
    (fun hZ => Ch3E215M.le_normalizer_of_isTISetIn hp inf_le_left hTI hZ) hdata
  have h2 := Ch3E215M.two_le_relIndex hp hcharI hne
  rw [← Ch3E215M.relIndex_A_eq hp hcharI hne] at h2
  have hAeq : B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V) = A := by
    rw [hp.conjSub_kerIn_inf_eq, hA, e]
  have hAO : A ≤ pCoreOf 2 I := hAeq ▸ hp.A_le_pCoreOf
  rw [hAeq] at hcount h2
  have hAN : A ≤ Subgroup.normalizer (V : Set Γ) := hAO.trans hp.pCoreOf_le_normalizer
  rw [E2.rAV_autI hAN]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (B6.isPGroup_of_isElemAbelian h.elem)
  obtain ⟨l, hl⟩ := IsPGroup.iff_card.1
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).to_le hAO)
  exact E2.ratio_lt_two (hn ▸ E2.relIndex_dvd_card _ _ inf_le_left)
    (hl ▸ E2.relIndex_dvd_card _ _ inf_le_left) (by omega) hcount

end CFSG.Quasithin.SimsE2
