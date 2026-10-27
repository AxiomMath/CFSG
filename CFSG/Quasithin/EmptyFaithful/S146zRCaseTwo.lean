module

public import CFSG.Quasithin.EmptyFaithful.S146zRElem
public import CFSG.Quasithin.EmptyFaithful.S146zQAut
public import CFSG.Quasithin.EmptyFaithful.SBc15C2Aut
public import CFSG.Quasithin.EmptyFaithful.S146zRQFour

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.GoldS146P

section CaseTwo

theorem q_not_solvable_of_simple {L : Type*} [Group L] [IsSimpleGroup L]
    (hnc : ∃ a b : L, a * b ≠ b * a) : ¬ Group.IsSolvable L := by
  intro hs
  obtain ⟨a, b, hab⟩ := hnc
  have hn : (commutator L).Normal := inferInstance
  rcases hn.eq_bot_or_eq_top with h | h
  · apply hab
    have h1 : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊥ := h
    have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1 (Subgroup.mem_top a)
    exact (Subgroup.mem_centralizer_iff.mp h2 b (Subgroup.mem_top b)).symm
  · have : Group.IsPerfect L := ⟨h⟩
    have : Nontrivial L := ⟨⟨a * b, b * a, hab⟩⟩
    exact Group.IsPerfect.not_isSolvable L hs

theorem q_ker_eq_pCore_of_surjective {K L : Type*} [Group K] [Finite K] [Group L] [IsSimpleGroup L]
    (hnc : ∃ a b : L, a * b ≠ b * a) (θ : K →* L) (hθ : Function.Surjective θ)
    (hker : IsPGroup 2 θ.ker) : θ.ker = CFSG.Open.pCore 2 K := by
  refine le_antisymm (le_pCore 2 (MonoidHom.normal_ker θ) hker) ?_
  have hp2 : IsPGroup 2 (CFSG.Open.pCore 2 K) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hn : ((CFSG.Open.pCore 2 K).map θ).Normal :=
    (CFSG.LieType.BorelTits.pCore_normal 2).map θ hθ
  rcases hn.eq_bot_or_eq_top with h | h
  · exact (Subgroup.map_eq_bot_iff _).mp h
  · exfalso
    apply q_not_solvable_of_simple hnc
    have : Group.IsNilpotent ↥(CFSG.Open.pCore 2 K) := hp2.isNilpotent
    have hsolv : Group.IsSolvable ↥(CFSG.Open.pCore 2 K) := inferInstance
    refine Group.isSolvable_of_surjective (f := θ.comp (CFSG.Open.pCore 2 K).subtype) ?_
    intro y
    have hy : y ∈ (CFSG.Open.pCore 2 K).map θ := h ▸ Subgroup.mem_top y
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem q_stage14614C2 (h12 : Stage14612PartP) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (iS : Input14614NoSz) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) {K₁ : Subgroup G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hp3 : p = 3)
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : Nonempty (OTwoQuot (K₁ ⊔ T) ≃* MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))) :
    Stage14614C2 T H p := by
  classical
  subst hp3
  obtain ⟨ι⟩ := e
  refine ⟨rfl, by rw [hKz]; exact hK₁, n, hn, ?_⟩
  have hn3 : 3 ≤ n := by omega
  have hLs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := sl_simple n hn3
  have hnc := sl_nonabelian n hn3
  have hK₁G : K₁ ≤ mcOf T := le_of_mem_cComp hK₁
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hTG : T ≤ mcOf T := hred.isHTM.1.1.trans hHG
  have hnorm : mcOf T ≤ Subgroup.normalizer (K₁ : Set G) := by
    rw [← hKz]
    exact le_normalizer_conjClosure _ _
  have hKTG : K₁ ⊔ T ≤ mcOf T := sup_le hK₁G hTG
  let ψ : ↥(K₁ ⊔ T) →* MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    ι.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(K₁ ⊔ T)))
  have hψ : Function.Surjective ψ := ι.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker = CFSG.Open.pCore 2 ↥(K₁ ⊔ T) := by
    ext x
    change ι (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hker2 : IsPGroup 2 ψ.ker := hψker ▸ CFSG.LieType.BorelTits.pCore_isPGroup 2
  let j : ↥K₁ →* ↥(K₁ ⊔ T) := Subgroup.inclusion le_sup_left
  have hj : Function.Injective j := Subgroup.inclusion_injective _
  have hjn : j.range.Normal := by
    rw [Subgroup.inclusion_range]
    exact Subgroup.normal_subgroupOf_of_le_normalizer (hKTG.trans hnorm)
  have : Group.IsPerfect ↥K₁ := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK₁)
  have : Nontrivial ↥K₁ := (Subgroup.nontrivial_iff_ne_bot _).mpr (ne_bot_of_mem_cComp hK₁)
  obtain ⟨θ, hθ, hθker⟩ := SBc15.exists_theta_sl hn ψ hψ hker2 j hj hjn
  have hkerθ : θ.ker = CFSG.Open.pCore 2 ↥K₁ := q_ker_eq_pCore_of_surjective hnc θ hθ hθker
  let e₀ : OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hkerθ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθ)
  obtain ⟨eK⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hK₁)
  let e1 : ↥(imageOTwoQuot (mcOf T) K₁) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
    eK.symm.trans e₀
  have hNn : (imageOTwoQuot (mcOf T) K₁).Normal := q_normal_image_of_normal hK₁G hnorm
  have hZ := q_forall_comm_eq_one_of_equiv hnc e1
  obtain ⟨E, hE, hEel, hEc⟩ := q_exists_elemAbelian_image h12 S hred hmax
  have hEN : E ≤ imageOTwoQuot (mcOf T) K₁ :=
    hE.trans (q_image_mono (hKz ▸ le_conjClosure _ _))
  have hcen0 := q_centralizer_eq_bot h36 hlist iS S hred hmax (imageOTwoQuot (mcOf T) K₁) hZ
    ⟨E, hEN, hEel, hEc⟩ (fun h => absurd h (by norm_num))
  have hcen : ∀ x : OTwoQuot (mcOf T), (∀ y ∈ imageOTwoQuot (mcOf T) K₁, x * y = y * x) →
      x ∈ imageOTwoQuot (mcOf T) K₁ := by
    intro x hx
    have hxc : x ∈ Subgroup.centralizer
        (↑(imageOTwoQuot (mcOf T) K₁) : Set (OTwoQuot (mcOf T))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (hx h hh).symm
    rw [hcen0, Subgroup.mem_bot] at hxc
    rw [hxc]
    exact one_mem _
  let Φ : ↥(K₁ ⊔ T) →* OTwoQuot (mcOf T) := (qPi (mcOf T)).comp (Subgroup.inclusion hKTG)
  have hΦker : Φ.ker ≤ ψ.ker := by
    rw [hψker]
    refine le_pCore 2 (MonoidHom.normal_ker Φ) ?_
    have hle : Φ.ker ≤ (CFSG.Open.pCore 2 ↥(mcOf T)).comap (Subgroup.inclusion hKTG) := by
      intro x hx
      have hx' : (QuotientGroup.mk (Subgroup.inclusion hKTG x) : OTwoQuot (mcOf T)) = 1 :=
        MonoidHom.mem_ker.mp hx
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hKTG x)).mp hx'
    exact ((CFSG.LieType.BorelTits.pCore_isPGroup 2).comap_of_injective _
      (Subgroup.inclusion_injective hKTG)).to_le hle
  exact q_mulEquiv_mulAut_of_ker (imageOTwoQuot (mcOf T) K₁) hcen hZ e1 Φ ψ hψ hΦker

end CaseTwo

end CFSG.Quasithin
