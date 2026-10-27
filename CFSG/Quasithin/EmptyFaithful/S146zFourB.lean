module

public import CFSG.Quasithin.EmptyFaithful.S146zRank2
public import CFSG.Quasithin.EmptyFaithful.S146zFourA

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section Extract

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem FCtx.not_centralizer_le (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {y w : G}
    (hyH : y ∉ mcOf T) (hw : w ∈ U₁ ∨ w ∈ U₂) (hwZ : w ∉ Zz)
    (hw' : y * w * y⁻¹ ∈ U₁ ∨ y * w * y⁻¹ ∈ U₂) (hw'Z : y * w * y⁻¹ ∉ Zz) :
    ¬ Subgroup.centralizer ({u} : Set G) ≤ mcOf T := by
  intro hcen
  obtain ⟨h₁, hh₁, hh₁u⟩ := c.pure_conj S hw hwZ
  obtain ⟨h₂, hh₂, hh₂u⟩ := c.pure_conj S hw' hw'Z
  have hxu : (h₂⁻¹ * y * h₁) * u * (h₂⁻¹ * y * h₁)⁻¹ = u := by
    calc (h₂⁻¹ * y * h₁) * u * (h₂⁻¹ * y * h₁)⁻¹
        = h₂⁻¹ * y * (h₁ * u * h₁⁻¹) * y⁻¹ * h₂ := by group
      _ = h₂⁻¹ * (y * w * y⁻¹) * h₂ := by rw [hh₁u]; group
      _ = h₂⁻¹ * (h₂ * u * h₂⁻¹) * h₂ := by rw [hh₂u]
      _ = u := by group
  have hxC : h₂⁻¹ * y * h₁ ∈ Subgroup.centralizer ({u} : Set G) := by
    have hcomm : (h₂⁻¹ * y * h₁) * u = u * (h₂⁻¹ * y * h₁) := by
      calc (h₂⁻¹ * y * h₁) * u
          = ((h₂⁻¹ * y * h₁) * u * (h₂⁻¹ * y * h₁)⁻¹) * (h₂⁻¹ * y * h₁) := by group
        _ = u * (h₂⁻¹ * y * h₁) := by rw [hxu]
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact hcomm.symm
  have hxH := hcen hxC
  apply hyH
  have e : y = h₂ * (h₂⁻¹ * y * h₁) * h₁⁻¹ := by group
  rw [e]
  exact (mcOf T).mul_mem ((mcOf T).mul_mem hh₂ hxH) ((mcOf T).inv_mem hh₁)

theorem Setting146.mem_mcOf_of_conj_mem_Z (S : Setting146 G T M) {y z : G} (hz : z ∈ Zz) (hz1 : z ≠ 1)
    (hy : y * z * y⁻¹ ∈ Zz) : y ∈ mcOf T := by
  have hzy : y * z * y⁻¹ = z := by
    symm
    refine S.Z_eq_of_iff hz hy ?_
    constructor
    · intro h; exact absurd h hz1
    · intro h
      have e : z = y⁻¹ * (y * z * y⁻¹) * y := by group
      rw [e, h]; group
  rw [← S.normalizer_Z]
  have hyc : y ∈ Subgroup.centralizer (Zz : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1]; simp
    · have haz : a = z := S.Z_eq_of_iff ha hz (by simp [ha1, hz1])
      rw [haz]
      exact (mul_inv_eq_iff_eq_mul.mp hzy).symm
  exact Subgroup.centralizer_le_normalizer _ hyc

theorem FCtx.vanish (S : Setting146 G T M) (h4 : Stage1463Four) (c : FCtx T M K U₁ U₂ s u) {y w : G}
    (hyH : y ∉ mcOf T) (hcen : Subgroup.centralizer ({u} : Set G) ≤ mcOf T)
    (hw : w ∈ U₁ ∨ w ∈ U₂) (hw' : y * w * y⁻¹ ∈ U₁ ∨ y * w * y⁻¹ ∈ U₂) : w = 1 := by
  by_contra hw1
  have hw'1 : y * w * y⁻¹ ≠ 1 := fun h => hw1 (by
    have e : w = y⁻¹ * (y * w * y⁻¹) * y := by group
    rw [e, h]; group)
  by_cases hwZ : w ∈ Zz
  · by_cases hw'Z : y * w * y⁻¹ ∈ Zz
    · exact hyH (S.mem_mcOf_of_conj_mem_Z hwZ hw1 hw'Z)
    · exact c.pure_not_conj S h4 hw' hw'Z y w hwZ hw1 rfl
  · by_cases hw'Z : y * w * y⁻¹ ∈ Zz
    · exact c.pure_not_conj S h4 hw hwZ y⁻¹ (y * w * y⁻¹) hw'Z hw'1 (by group)
    · exact c.not_centralizer_le S hyH hw hwZ hw' hw'Z hcen

end Extract

section CaseII

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem FCtx.false_of_rank_two_one (S : Setting146 G T M) (h4 : Stage1463Four) (c : FCtx T M K U₁ U₂ s u)
    {γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)}
    (hsetup : F8Setup T (VZ T M) (yOfL22 T M) (mcOf T) γ γ' g)
    (hin : ∀ b ∈ F8.Uγ (VZ T M) (mcOf T) (g : G), conjSub b U₁ = U₁)
    (h2 : mIdx (uOfL22 T M) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) = 1)
    (hlt : 2 < mIdx (uOfL22 T M)
      (centralizerMod Zz (uOfL22 T M) (F8.Uγ (VZ T M) (mcOf T) (g : G)))) : False := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUp : IsPGroup 2 (uOfL22 T M) := isPGroup_of_isElemAbelian hUab
  have hcommU : ∀ a ∈ uOfL22 T M, ∀ b ∈ uOfL22 T M, a * b = b * a := fun a ha b hb =>
    S.comm_of_mem_conjClosure ha hb
  have hUgH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T := hF98.Uγ_le_H hsetup
  set Ug := F8.Uγ (VZ T M) (mcOf T) (g : G) with hUg
  set D := F8.DH (VZ T M) Zz (mcOf T) (g : G) with hD
  have hrelD : D.relIndex (uOfL22 T M) = 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hUp, h2]; norm_num
  have hrelC : 8 ≤ (centralizerMod Zz (uOfL22 T M) Ug).relIndex (uOfL22 T M) := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hUp]
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hlt
  have key : ∃ d b, d ∈ D ∧ (d ∈ U₁ ∨ d ∈ U₂) ∧ b ∈ Ug ∧ d * b * d⁻¹ * b⁻¹ ≠ 1 := by
    by_contra hno
    push Not at hno
    have hAC : D ⊓ U₁ ≤ centralizerMod Zz (uOfL22 T M) Ug := fun d hd =>
      ⟨c.hU₁U hd.2, S.conjClosure_le_normalizer_Z hG (c.hU₁U hd.2), fun b hb => by
        rw [hno d b hd.1 (Or.inl hd.2) hb]; exact Subgroup.one_mem _⟩
    have hBC : D ⊓ U₂ ≤ centralizerMod Zz (uOfL22 T M) Ug := fun d hd =>
      ⟨c.hU₂U hd.2, S.conjClosure_le_normalizer_Z hG (c.hU₂U hd.2), fun b hb => by
        rw [hno d b hd.1 (Or.inr hd.2) hb]; exact Subgroup.one_mem _⟩
    have hCC : cuOf T M ≤ centralizerMod Zz (uOfL22 T M) Ug := centralizerMod_anti_right _ hUgH
    have hNC : (D ⊓ U₁) ⊔ (D ⊓ U₂) ⊔ cuOf T M ≤ centralizerMod Zz (uOfL22 T M) Ug :=
      sup_le (sup_le hAC hBC) hCC
    obtain ⟨b₁, hb₁U, hb₁⟩ := exists_rep_of_relIndex_two c.hU₁U hrelD
    obtain ⟨b₂, hb₂U, hb₂⟩ := exists_rep_of_relIndex_two c.hU₂U hrelD
    have hb₁' : b₁ ∈ uOfL22 T M := c.hU₁U hb₁U
    have hb₂' : b₂ ∈ uOfL22 T M := c.hU₂U hb₂U
    have hN4 : ((D ⊓ U₁) ⊔ (D ⊓ U₂) ⊔ cuOf T M).relIndex (uOfL22 T M) ≤ 4 := by
      refine (relIndex_le_card_of_cover ({1, b₁, b₂, b₁ * b₂} : Finset G) ?_ ?_).trans
        Finset.card_le_four
      · intro r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Subgroup.one_mem _
        · exact hb₁'
        · exact hb₂'
        · exact (uOfL22 T M).mul_mem hb₁' hb₂'
      · intro v hv
        obtain ⟨y, hy, r₂, hr₂, d, hd, rfl⟩ := c.exists_decomp3 S hv
        have hyU := c.hU₁U hy
        have hr₂U := c.hU₂U hr₂
        have hdU := cuOf_le T M hd
        have hre : ∀ a b : G, a ∈ uOfL22 T M → b ∈ uOfL22 T M →
            y * (r₂ * d) * (a * b) = (y * a) * (r₂ * b) * d := by
          intro a b ha hb
          calc y * (r₂ * d) * (a * b) = y * r₂ * (d * a) * b := by group
            _ = y * r₂ * (a * d) * b := by rw [hcommU d hdU a ha]
            _ = y * (r₂ * a) * d * b := by group
            _ = y * (a * r₂) * d * b := by rw [hcommU r₂ hr₂U a ha]
            _ = y * a * r₂ * (d * b) := by group
            _ = y * a * r₂ * (b * d) := by rw [hcommU d hdU b hb]
            _ = (y * a) * (r₂ * b) * d := by group
        have hdN : d ∈ (D ⊓ U₁) ⊔ (D ⊓ U₂) ⊔ cuOf T M := Subgroup.mem_sup_right hd
        rcases hb₁ y hy with h₁ | h₁ <;> rcases hb₂ r₂ hr₂ with h₂ | h₂
        · refine ⟨b₁ * b₂, by simp, ?_⟩
          rw [hre b₁ b₂ hb₁' hb₂']
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left h₁))
            (Subgroup.mem_sup_left (Subgroup.mem_sup_right h₂))) hdN
        · refine ⟨b₁, by simp, ?_⟩
          have := hre b₁ 1 hb₁' (Subgroup.one_mem _)
          simp only [mul_one] at this
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left h₁))
            (Subgroup.mem_sup_left (Subgroup.mem_sup_right h₂))) hdN
        · refine ⟨b₂, by simp, ?_⟩
          have := hre 1 b₂ (Subgroup.one_mem _) hb₂'
          simp only [one_mul, mul_one] at this
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left h₁))
            (Subgroup.mem_sup_left (Subgroup.mem_sup_right h₂))) hdN
        · refine ⟨1, by simp, ?_⟩
          rw [mul_one]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left h₁))
            (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right h₂)) hdN)
    have hdvd := Subgroup.relIndex_dvd_of_le_left (uOfL22 T M) hNC
    have hNpos : 0 < ((D ⊓ U₁) ⊔ (D ⊓ U₂) ⊔ cuOf T M).relIndex (uOfL22 T M) :=
      Nat.pos_of_ne_zero (relIndex_ne_zero_fin _ _)
    have := Nat.le_of_dvd hNpos hdvd
    omega
  obtain ⟨d, b, hdD, hdU, hbUg, hne⟩ := key
  have hcomm : d * b * d⁻¹ * b⁻¹ ∈ conjSub (g : G) Zz := hdD.2.2 b hbUg
  have hdU' : d * b * d⁻¹ * b⁻¹ ∈ U₁ ∨ d * b * d⁻¹ * b⁻¹ ∈ U₂ := by
    rcases hdU with hd1 | hd2
    · left
      have haN₁ : b ∈ Subgroup.normalizer (U₁ : Set G) := mem_normalizer_of_conjSub_eq (hin b hbUg)
      have h1 : b * d⁻¹ * b⁻¹ ∈ U₁ := (Subgroup.mem_normalizer_iff.mp haN₁ d⁻¹).mp (U₁.inv_mem hd1)
      have e : d * b * d⁻¹ * b⁻¹ = d * (b * d⁻¹ * b⁻¹) := by group
      rw [e]; exact U₁.mul_mem hd1 h1
    · right
      have haN₂ : b ∈ Subgroup.normalizer (U₂ : Set G) :=
        mem_normalizer_of_conjSub_eq (c.conjSub_U₂ S (hUgH hbUg) (hin b hbUg))
      have h1 : b * d⁻¹ * b⁻¹ ∈ U₂ := (Subgroup.mem_normalizer_iff.mp haN₂ d⁻¹).mp (U₂.inv_mem hd2)
      have e : d * b * d⁻¹ * b⁻¹ = d * (b * d⁻¹ * b⁻¹) := by group
      rw [e]; exact U₂.mul_mem hd2 h1
  obtain ⟨z, hz, hz1, hzx⟩ : ∃ z ∈ Zz, z ≠ 1 ∧ (g : G) * z * (g : G)⁻¹ = d * b * d⁻¹ * b⁻¹ := by
    refine ⟨(g : G)⁻¹ * (d * b * d⁻¹ * b⁻¹) * g, mem_conjSub.mp hcomm, ?_, by group⟩
    intro h1
    apply hne
    have e : d * b * d⁻¹ * b⁻¹ = (g : G) * ((g : G)⁻¹ * (d * b * d⁻¹ * b⁻¹) * g) * (g : G)⁻¹ := by
      group
    rw [e, h1]; group
  have hxZ : d * b * d⁻¹ * b⁻¹ ∉ Zz := hzx ▸ S.conj_not_mem_Z hG hsetup hz hz1
  exact c.pure_not_conj S h4 hdU' hxZ g z hz hz1 hzx

end CaseII

section CaseI

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

omit [Finite G] in
theorem commutator_le_comm {W V U : Subgroup G} (h : V ≤ U) : ⁅W, V⁆ ≤ ⁅U, W⁆ := by
  rw [Subgroup.commutator_comm W V]
  exact Subgroup.commutator_mono h le_rfl

theorem FCtx.J_le₁ (c : FCtx T M K U₁ U₂ s u) {W : Subgroup G} (hin : ∀ b ∈ W, conjSub b U₁ = U₁) :
    Zz ⊔ ⁅W, U₁⁆ ≤ U₁ := sup_le c.hSec.le (commutator_le_of_conjSub_eq hin)

theorem FCtx.J_le₂ (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {W : Subgroup G}
    (hWH : W ≤ mcOf T) (hin : ∀ b ∈ W, conjSub b U₁ = U₁) : Zz ⊔ ⁅W, U₂⁆ ≤ U₂ :=
  sup_le c.hZU₂ (c.commutator_le_U₂ S hWH hin)

theorem FCtx.J_inf (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {W : Subgroup G}
    (hWH : W ≤ mcOf T) (hin : ∀ b ∈ W, conjSub b U₁ = U₁) :
    (Zz ⊔ ⁅W, U₁⁆) ⊓ (Zz ⊔ ⁅W, U₂⁆) = Zz := by
  apply le_antisymm
  · calc (Zz ⊔ ⁅W, U₁⁆) ⊓ (Zz ⊔ ⁅W, U₂⁆) ≤ U₁ ⊓ U₂ :=
          inf_le_inf (c.J_le₁ hin) (c.J_le₂ S hWH hin)
      _ = Zz := c.inf_U₂_eq
  · exact le_inf le_sup_left le_sup_left

theorem FCtx.J_sup (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {W : Subgroup G}
    (hWH : W ≤ mcOf T) : (Zz ⊔ ⁅W, U₁⁆) ⊔ (Zz ⊔ ⁅W, U₂⁆) = ⁅uOfL22 T M, W⁆ ⊔ Zz :=
  le_antisymm (sup_le (sup_le le_sup_right ((commutator_le_comm c.hU₁U).trans le_sup_left))
      (sup_le le_sup_right ((commutator_le_comm c.hU₂U).trans le_sup_left)))
    (c.commutator_sup_le S hWH)

theorem FCtx.false_of_symmetric (S : Setting146 G T M) (h4 : Stage1463Four) (c : FCtx T M K U₁ U₂ s u)
    {Wg Wd : Subgroup G} {y : G}
    (hWgH : Wg ≤ mcOf T) (hWdH : Wd ≤ mcOf T)
    (hin₁ : ∀ b ∈ Wg, conjSub b U₁ = U₁) (hin₂ : ∀ b ∈ Wd, conjSub b U₁ = U₁)
    (hyWg : conjSub y Wg = uOfL22 T M) (hWd : Wd = conjSub y (uOfL22 T M))
    (hA : conjSub y⁻¹ Zz ≤ ⁅uOfL22 T M, Wg⁆) (hyH : y ∉ mcOf T)
    (hcen : Subgroup.centralizer ({u} : Set G) ≤ mcOf T) : False := by
  classical
  have hcommU : ∀ a ∈ uOfL22 T M, ∀ b ∈ uOfL22 T M, a * b = b * a := fun a ha b hb =>
    S.comm_of_mem_conjClosure ha hb
  have hZU : Zz ≤ uOfL22 T M := Z_le_conjClosure_VZ T M (mcOf T)
  have hS₀U : ⁅uOfL22 T M, Wg⁆ ≤ uOfL22 T M :=
    S145.commutator_le_of_le_normalizer (hWgH.trans (le_normalizer_conjClosure _ _))
  have hcU : conjSub y⁻¹ Wd = uOfL22 T M := by rw [hWd, conjSub_conjSub_inv]
  have hcU' : conjSub y⁻¹ (uOfL22 T M) = Wg := by rw [← hyWg, conjSub_conjSub_inv]
  have hS₀eq : conjSub y⁻¹ ⁅uOfL22 T M, Wd⁆ = ⁅uOfL22 T M, Wg⁆ := by
    rw [conjSub_commutator', hcU, hcU', Subgroup.commutator_comm]
  have hJ'le : ∀ (V : Subgroup G), V ≤ uOfL22 T M →
      conjSub y⁻¹ (Zz ⊔ ⁅Wd, V⁆) ≤ ⁅uOfL22 T M, Wg⁆ := by
    intro V hV
    rw [conjSub_sup]
    refine sup_le hA ?_
    calc conjSub y⁻¹ ⁅Wd, V⁆ ≤ conjSub y⁻¹ ⁅uOfL22 T M, Wd⁆ :=
          conjSub_mono _ (commutator_le_comm hV)
      _ = ⁅uOfL22 T M, Wg⁆ := hS₀eq
  have hJ'sup : conjSub y⁻¹ (Zz ⊔ ⁅Wd, U₁⁆) ⊔ conjSub y⁻¹ (Zz ⊔ ⁅Wd, U₂⁆) = ⁅uOfL22 T M, Wg⁆ := by
    apply le_antisymm
    · exact sup_le (hJ'le U₁ c.hU₁U) (hJ'le U₂ c.hU₂U)
    · have h1 : conjSub y⁻¹ (Zz ⊔ ⁅Wd, U₁⁆) ⊔ conjSub y⁻¹ (Zz ⊔ ⁅Wd, U₂⁆) =
          conjSub y⁻¹ (⁅uOfL22 T M, Wd⁆ ⊔ Zz) := by
        rw [← conjSub_sup, c.J_sup S hWdH]
      rw [h1, conjSub_sup, hS₀eq]
      exact le_sup_left
  have hJ'inf : conjSub y⁻¹ (Zz ⊔ ⁅Wd, U₁⁆) ⊓ conjSub y⁻¹ (Zz ⊔ ⁅Wd, U₂⁆) = conjSub y⁻¹ Zz := by
    rw [← conjSub_inf, c.J_inf S hWdH hin₂]
  have hJ'mem₁ : ∀ w ∈ conjSub y⁻¹ (Zz ⊔ ⁅Wd, U₁⁆), y * w * y⁻¹ ∈ U₁ := by
    intro w hw
    have h1 : y⁻¹⁻¹ * w * y⁻¹ ∈ Zz ⊔ ⁅Wd, U₁⁆ := mem_conjSub.mp hw
    rw [inv_inv] at h1
    exact c.J_le₁ hin₂ h1
  have hJ'mem₂ : ∀ w ∈ conjSub y⁻¹ (Zz ⊔ ⁅Wd, U₂⁆), y * w * y⁻¹ ∈ U₂ := by
    intro w hw
    have h1 : y⁻¹⁻¹ * w * y⁻¹ ∈ Zz ⊔ ⁅Wd, U₂⁆ := mem_conjSub.mp hw
    rw [inv_inv] at h1
    exact c.J_le₂ S hWdH hin₂ h1
  have hvan : ∀ w : G, (w ∈ U₁ ∨ w ∈ U₂) → (y * w * y⁻¹ ∈ U₁ ∨ y * w * y⁻¹ ∈ U₂) → w = 1 :=
    fun w hw hw' => c.vanish S h4 hyH hcen hw hw'
  have h12' : (Zz ⊔ ⁅Wg, U₁⁆) ⊓ conjSub y⁻¹ (Zz ⊔ ⁅Wd, U₂⁆) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    exact hvan w (Or.inl (c.J_le₁ hin₁ hw.1)) (Or.inr (hJ'mem₂ w hw.2))
  have h21' : (Zz ⊔ ⁅Wg, U₂⁆) ⊓ conjSub y⁻¹ (Zz ⊔ ⁅Wd, U₁⁆) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    exact hvan w (Or.inr (c.J_le₂ S hWgH hin₁ hw.1)) (Or.inl (hJ'mem₁ w hw.2))
  have hZc : Nat.card Zz = 2 := S.card_Z
  have hAc : Nat.card (conjSub y⁻¹ Zz) = 2 := (natCard_conjSub_eq y⁻¹ Zz).trans hZc
  have hTU : ⁅uOfL22 T M, Wg⁆ ⊔ Zz ≤ uOfL22 T M := sup_le hS₀U hZU
  have hTS : Nat.card ↥(⁅uOfL22 T M, Wg⁆ ⊔ Zz) ≤ 2 * Nat.card ↥⁅uOfL22 T M, Wg⁆ := by
    obtain ⟨hc, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute ⁅uOfL22 T M, Wg⁆ Zz
      (fun x hx y hy => hcommU x (hS₀U hx) y (hZU hy))
    rw [hZc] at hc
    have hpos : 0 < Nat.card ↥(⁅uOfL22 T M, Wg⁆ ⊓ Zz) := Nat.card_pos
    nlinarith
  have hJsup := c.J_sup S hWgH
  exact card_contra_of_decomp (J₁ := Zz ⊔ ⁅Wg, U₁⁆) (J₂ := Zz ⊔ ⁅Wg, U₂⁆)
    (J₁' := conjSub y⁻¹ (Zz ⊔ ⁅Wd, U₁⁆)) (J₂' := conjSub y⁻¹ (Zz ⊔ ⁅Wd, U₂⁆))
    (T := ⁅uOfL22 T M, Wg⁆ ⊔ Zz) (S := ⁅uOfL22 T M, Wg⁆) (Z := Zz) (A := conjSub y⁻¹ Zz)
    (fun x hx y hy => hcommU x (hTU hx) y (hTU hy))
    (le_sup_left.trans hJsup.le) (le_sup_right.trans hJsup.le)
    (hJ'le U₁ c.hU₁U) (hJ'le U₂ c.hU₂U) le_sup_left hJsup hJ'sup (c.J_inf S hWgH hin₁) hJ'inf hZc hAc
    hTS h12' h21'

end CaseI

section FourB

theorem input14624FourB_of (h4 : Stage1463Four) : Input14624FourB := by
  intro G _ _ T M S hB K U₁ U₂ s u γ γ' g hfull h3 h2 hinv h1
  classical
  obtain ⟨hctx, -, hgeom⟩ := hfull
  obtain ⟨hsetup, hDlt, hpos, hle, hlt, -⟩ := hgeom
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2
  have c : FCtx T M K U₁ U₂ s u := FCtx.ofCtx24 S hctx h3 h2 hinv
  have hpos' : 0 < mIdx (uOfL22 T M)
      (F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) := hpos
  have hle' : mIdx (uOfL22 T M) (F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) ≤
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
        (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) := hle
  have hlt' : mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
        (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) <
      mIdx (uOfL22 T M) (centralizerMod (quasithinOmegaOneCenter T) (uOfL22 T M)
        (F8.Uγ (VZ T M) (mcOf T) (g : G))) := hlt
  have hle2 : mIdx (uOfL22 T M) (F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) ≤ 2 := by
    omega
  have hin := c.inner_of_rank_two S hsetup h1 hle2
  have hcase : mIdx (uOfL22 T M) (F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) = 1 ∨
      mIdx (uOfL22 T M) (F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) = 2 := by
    omega
  rcases hcase with hD1 | hD2
  · exfalso
    exact c.false_of_rank_two_one S h4 hsetup hin hD1 (by omega)
  · intro hcen
    have hA₁ := A₁_le_commutator_strict S hle' hlt'
    have hn := hF98.not_Vγ_le_ballStab_of_lt hsetup hDlt
    obtain ⟨δ, δ', k, y, hsetup', hyγ, hyγ₁, hUδ, hUy, hDHδ, hDγδ⟩ :=
      hF98.exists_symmetric_setup hsetup hn
    have h1δ : mIdx (F8.Uγ (VZ T M) (mcOf T) (k : G))
        (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (k : G)) = 2 := by
      rw [hUδ, hDγδ, F9.mIdx_conjSub]
      exact hD2
    have hleδ : mIdx (uOfL22 T M)
        (F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (k : G)) ≤ 2 := by
      rw [hDHδ]
      have e : uOfL22 T M = conjSub (y : G) (F8.Uγ (VZ T M) (mcOf T) (g : G)) := hUy.symm
      rw [e, F9.mIdx_conjSub, h1]
    have hinδ := c.inner_of_rank_two S hsetup' h1δ hleδ
    have hUgH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T := hF98.Uγ_le_H hsetup
    have hUdH : F8.Uγ (VZ T M) (mcOf T) (k : G) ≤ mcOf T := hF98.Uγ_le_H hsetup'
    have hygH : (y : G) * (g : G) ∈ mcOf T := by
      have h1'' : (y * g) • F8.γ₁ T (yOfL22 T M) (mcOf T) = F8.γ₁ T (yOfL22 T M) (mcOf T) := by
        rw [mul_smul, hsetup.edge₁, hyγ]
      have := mem_stab_of_smul_eq h1''
      rwa [stab_γ₁ hF98.amalgamHypV.le₂] at this
    have hyH : (y : G) ∉ mcOf T := by
      intro hyH
      have hgH : (g : G) ∈ mcOf T := by
        have e : (g : G) = (y : G)⁻¹ * ((y : G) * (g : G)) := by group
        rw [e]
        exact (mcOf T).mul_mem ((mcOf T).inv_mem hyH) hygH
      obtain ⟨z₀, hz₀, hz₀1⟩ := S.exists_ne_one_Z
      apply S.conj_not_mem_Z hG hsetup hz₀ hz₀1
      have hgN : (g : G) ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
        S.normalizer_Z.ge hgH
      exact (Subgroup.mem_normalizer_iff.mp hgN z₀).mp hz₀
    have hygN : (y : G) * (g : G) ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
      rw [S.normalizer_Z]; exact hygH
    have hA : conjSub (y : G)⁻¹ (quasithinOmegaOneCenter T) ≤
        ⁅uOfL22 T M, F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ := by
      have e : conjSub (y : G)⁻¹ (quasithinOmegaOneCenter T) =
          F8.A₁ (quasithinOmegaOneCenter T) (g : G) := by
        have e1 : F8.A₁ (quasithinOmegaOneCenter T) (g : G) =
            conjSub (g : G) (quasithinOmegaOneCenter T) := rfl
        rw [e1]
        have e2 : (g : G) = (y : G)⁻¹ * ((y : G) * (g : G)) := by group
        calc conjSub (y : G)⁻¹ (quasithinOmegaOneCenter T)
            = conjSub (y : G)⁻¹ (conjSub ((y : G) * (g : G)) (quasithinOmegaOneCenter T)) := by
              rw [conjSub_eq_of_mem_normalizer hygN]
          _ = conjSub ((y : G)⁻¹ * ((y : G) * (g : G))) (quasithinOmegaOneCenter T) :=
              (conjSub_mul _ _ _).symm
          _ = conjSub (g : G) (quasithinOmegaOneCenter T) := by rw [← e2]
      rw [e]
      exact hA₁
    exact c.false_of_symmetric S h4 hUgH hUdH hin hinδ hUy hUδ hA hyH hcen

end FourB

end CFSG.Quasithin
