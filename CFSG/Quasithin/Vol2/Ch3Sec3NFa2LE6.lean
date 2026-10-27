module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2E6
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2KTC

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Blueprint
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem A2Cfg.normalizer_Z_le_normalizer_K0 (h36 : A36ForSQTK)
    (h128 : Lemma128Two) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (c : A2Cfg G T M L D H K q) :
    Subgroup.normalizer (a2Z T : Set G) ≤ Subgroup.normalizer (a2K0 K T : Set G) := by
  have hZ0 : a2Z T ≠ ⊥ :=
    quasithinOmegaOneCenter_ne_bot c.nf.hyp.sylow.1 c.nf.hyp.toSetup331.T_ne_bot
  have hZT : a2Z T ≤ T := (Subgroup.closure_le _).2 fun _ hz => hz.1.1
  have hP2 : IsPGroup 2 (a2Z T) := c.nf.hyp.sylow.1.to_le hZT
  have hloc : IsTwoLocal (Subgroup.normalizer (a2Z T : Set G)) := ⟨a2Z T, hZ0, hP2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hG2 : a2G2 K T ≤ Subgroup.centralizer (a2Z T : Set G) := c.G2_le_centralizer_Z h36
  have hKT : K ⊔ T ≤ Subgroup.normalizer (a2Z T : Set G) :=
    ((sup_le ((le_conjClosure K T).trans le_sup_left) le_sup_right).trans hG2).trans
      (Subgroup.centralizer_le_normalizer _)
  have hM'eq : M' = Subgroup.normalizer (conjClosure K T : Set G) :=
    (c.nf.uniqueM h128 h37 h38 h39).2 M' ⟨hM', hKT.trans hle⟩
  rw [← hM'eq]
  exact hle

theorem A2Cfg.TC_le_kerAct_K0 (c : A2Cfg G T M L D H K q) :
    a2TC K T ≤ kerAct (a2K0 K T) := by
  intro x hx
  have hG2N : a2G2 K T ≤ Subgroup.normalizer (a2K0 K T : Set G) :=
    sup_le Subgroup.le_normalizer (le_normalizer_conjClosure K T)
  have hxG : x ∈ a2G2 K T := pCoreOf_le 2 _ hx
  refine mem_kerAct.mpr ⟨hG2N hxG, fun k hk => ?_⟩
  have hkG : k ∈ a2G2 K T := Subgroup.mem_sup_left hk
  have h1 : x * k * x⁻¹ * k⁻¹ ∈ a2K0 K T :=
    (a2K0 K T).mul_mem ((Subgroup.mem_normalizer_iff.mp (hG2N hxG) k).mp hk)
      ((a2K0 K T).inv_mem hk)
  have h2 : x * k * x⁻¹ * k⁻¹ ∈ a2TC K T := by
    have e : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx
      (conj_mem_pCoreOf_of_mem_normalizer (Subgroup.le_normalizer hkG) ((a2TC K T).inv_mem hx))
  have hXN : a2K0 K T ≤ Subgroup.normalizer ((a2K0 K T ⊓ a2TC K T : Subgroup G) : Set G) :=
    F7.le_normalizer_inf Subgroup.le_normalizer
      (fun y hy => le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hy))
  have hXle : a2K0 K T ⊓ a2TC K T ≤ a2N0 K T :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hXN
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
  exact hXle (Subgroup.mem_inf.mpr ⟨h1, h2⟩)

theorem A2Cfg.K0_inf_kerAct_le_TC (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (c : A2Cfg G T M L D H K q) :
    a2K0 K T ⊓ kerAct (a2K0 K T) ≤ a2TC K T := by
  obtain ⟨t, ht, htK, hK', hKK₀, -⟩ := c.kstruct h37 h38
  set K' := K.map (MulAut.conj t).toMonoidHom with hK'def
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_mem_cComp c.nf.K_comp hK'
  have hKN' : K ≤ Subgroup.normalizer (K' : Set G) := le_normalizer_of_mem_cComp hK' c.nf.K_comp
  have hKK : K ≤ a2K0 K T := le_conjClosure K T
  have hK'K : K' ≤ a2K0 K T := by
    show K' ≤ conjClosure K T
    rw [hKK₀]
    exact le_sup_right
  have hK0N : a2K0 K T ≤ Subgroup.normalizer (K : Set G) := by
    show conjClosure K T ≤ _
    rw [hKK₀]
    exact sup_le Subgroup.le_normalizer hK'N
  have hK0N' : a2K0 K T ≤ Subgroup.normalizer (K' : Set G) := by
    show conjClosure K T ≤ _
    rw [hKK₀]
    exact sup_le hKN' Subgroup.le_normalizer
  intro x hx
  obtain ⟨hxK0, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxC' := (mem_kerAct.mp hxC).2
  have hKO : ∀ J : Subgroup G, J ≤ a2K0 K T → J ⊓ pCoreOf 2 (a2K0 K T) ≤ pCoreOf 2 J := by
    intro J hJ
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact F7.le_normalizer_inf Subgroup.le_normalizer
      (fun y hy => le_normalizer_pCoreOf 2 _ (hJ hy))
  have hxK : x ∈ kerAct K := by
    refine mem_kerAct.mpr ⟨hK0N hxK0, fun k hk => ?_⟩
    have h1 : x * k * x⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hK0N hxK0) k).mp hk) (K.inv_mem hk)
    exact hKO K hKK (Subgroup.mem_inf.mpr ⟨h1, hxC' k (hKK hk)⟩)
  have hxK' : x ∈ kerAct K' := by
    refine mem_kerAct.mpr ⟨hK0N' hxK0, fun k hk => ?_⟩
    have h1 : x * k * x⁻¹ * k⁻¹ ∈ K' :=
      K'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hK0N' hxK0) k).mp hk) (K'.inv_mem hk)
    exact hKO K' hK'K (Subgroup.mem_inf.mpr ⟨h1, hxC' k (hK'K hk)⟩)
  exact c.le_TC_of_acts_trivially h37 h38 ht htK
    (Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hxK0, Subgroup.mem_inf.mpr ⟨hxK, hxK'⟩⟩)

theorem leaf_E6ii_of (h36 : A36ForSQTK)
    (h128 : Lemma128Two) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    Leaf_E6ii := by
  intro G _ _ T M L D H K q facts g hg hZ
  have c := facts.cfg
  have hyp := facts.amalgam
  have hV0 := facts.V_ne
  obtain ⟨-, he1⟩ := facts.e1
  apply hg.critical.not_le
  have hgZ : (g : G) ∈ Subgroup.normalizer (a2Z T : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 hZ
  have hgK0 : (g : G) ∈ Subgroup.normalizer (a2K0 K T : Set G) :=
    c.normalizer_Z_le_normalizer_K0 h36 h128 h37 h38 h39 hgZ
  have hVst : a2V L T ≤ stab (g • γ₁ (a2G0 L K T) (a2G1 L T) (a2G2 K T)) :=
    V_le_stab_of_dist_le hyp hV0 hg.critical.dist_eq.le
  have hst : stab (g • γ₁ (a2G0 L K T) (a2G1 L T) (a2G2 K T)) = conjSub (g : G) (a2G2 K T) := by
    rw [stab_smul, stab_γ₁ hyp.le₂]
  rw [hst] at hVst
  have hbs : ballStab 1 (g • γ₁ (a2G0 L K T) (a2G1 L T) (a2G2 K T)) =
      conjSub (g : G) (a2TC K T) := by
    rw [ballStab_smul, (ballStab_one_γ₁ hyp.gen).1, he1]
  rw [hbs]
  have hG2N : a2G2 K T ≤ Subgroup.normalizer (a2K0 K T : Set G) :=
    sup_le Subgroup.le_normalizer (le_normalizer_conjClosure K T)
  have hconjN : ∀ y ∈ a2G2 K T, (g : G) * y * (g : G)⁻¹ ∈ Subgroup.normalizer (a2K0 K T : Set G) :=
    fun y hy => Subgroup.mul_mem _ (Subgroup.mul_mem _ hgK0 (hG2N hy)) (Subgroup.inv_mem _ hgK0)
  have hGγN : conjSub (g : G) (a2G2 K T) ≤ Subgroup.normalizer (a2K0 K T : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hconjN y hy
  set Dd : Subgroup G := conjSub (g : G) (a2G2 K T) ⊓ kerAct (a2K0 K T) with hDd
  have hDnorm : conjSub (g : G) (a2G2 K T) ≤ Subgroup.normalizer (Dd : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ y ∈ conjSub (g : G) (a2G2 K T), ∀ d ∈ Dd, y * d * y⁻¹ ∈ Dd := by
      intro y hy d hd
      obtain ⟨hdG, hdC⟩ := Subgroup.mem_inf.mp hd
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hdG) (Subgroup.inv_mem _ hy),
          conj_mem_kerAct_of_mem_normalizer (hGγN hy) hdC⟩
    intro d
    refine ⟨fun hd => key y hy d hd, fun hd => ?_⟩
    have h2 := key y⁻¹ (Subgroup.inv_mem _ hy) _ hd
    have e : y⁻¹ * (y * d * y⁻¹) * y⁻¹⁻¹ = d := by group
    rwa [e] at h2
  have hconjK0 : conjSub (g : G) (a2K0 K T) = a2K0 K T :=
    F7.conjSub_eq_of_mem_normalizer hgK0
  have hGγeq : conjSub (g : G) (a2G2 K T) = a2K0 K T ⊔ conjSub (g : G) T := by
    show (a2K0 K T ⊔ T).map _ = _
    rw [Subgroup.map_sup]
    show conjSub (g : G) (a2K0 K T) ⊔ conjSub (g : G) T = _
    rw [hconjK0]
  have hTgN : conjSub (g : G) T ≤ Subgroup.normalizer (a2K0 K T : Set G) :=
    fun y hy => hGγN (by
      rw [hGγeq]
      exact Subgroup.mem_sup_right hy)
  have hDK0 : IsPGroup 2 ↥(Dd ⊓ a2K0 K T) := by
    refine (pCoreOf_isPGroup 2 (a2G2 K T)).to_le ?_
    intro x hx
    obtain ⟨hxD, hxK0⟩ := Subgroup.mem_inf.mp hx
    exact c.K0_inf_kerAct_le_TC h37 h38
      (Subgroup.mem_inf.mpr ⟨hxK0, (Subgroup.mem_inf.mp hxD).2⟩)
  have hDp : IsPGroup 2 ↥Dd :=
    isPGroup_two_of_le_sup (F7.isPGroup_conjSub c.nf.hyp.sylow.1) hTgN
      (by rw [← hGγeq]; exact inf_le_left) hDK0
  have hVD : a2V L T ≤ Dd := by
    intro v hv
    have hvTC : v ∈ a2TC K T := facts.VTC hv
    exact Subgroup.mem_inf.mpr ⟨hVst hv, c.TC_le_kerAct_K0 hvTC⟩
  have hD2 : Dd ≤ pCoreOf 2 (conjSub (g : G) (a2G2 K T)) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hDnorm hDp
  rw [pCoreOf_conjSub] at hD2
  exact hVD.trans hD2

end CFSG.Quasithin.H13.NFa2
