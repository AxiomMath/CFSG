module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1FFW
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Kv

public section

namespace CFSG.Quasithin.H13

open Matrix CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.BlockPar CFSG.Open CFSG.Blueprint
  CFSG.QuasithinUnique
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_matrix)
open scoped Matrix

namespace PairStab

variable {n m : ℕ}

@[expose] def proj (h : 1 + m = n) (x : Fin n → ZMod 2) : Fin m → ZMod 2 :=
  x ∘ sumEquiv h ∘ Sum.inr

theorem proj_emb (h : 1 + m = n) (ξ : Fin m → ZMod 2) : proj h (emb h ξ) = ξ := by
  funext j
  simp [proj, emb]

theorem proj_add (h : 1 + m = n) (x y : Fin n → ZMod 2) :
    proj h (x + y) = proj h x + proj h y := by
  funext j
  simp [proj]

end PairStab

namespace Sec1211Ns

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  {S : Setting T L V V₁ V₂ n a₀ c₀} {m : ℕ} (F : Frame S m)

@[expose] noncomputable def crd₁ (g : G) : Fin m → ZMod 2 :=
  PairStab.proj F.h (((F.s⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₁.E g)

@[expose] noncomputable def crd₂ (g : G) : Fin m → ZMod 2 :=
  PairStab.proj F.h ((slGraphAut n (ZMod 2) F.s⁻¹ : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
    S.C₂.E g)

theorem crd₁_spec {a : G} (ha : a ∈ S.W₁) :
    S.C₁.E a = (F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ PairStab.emb F.h (crd₁ F a) := by
  obtain ⟨ξ, hξ⟩ := exists_emb₁ F ha
  have h1 : crd₁ F a = ξ := by
    rw [crd₁, hξ, VecStab.inv_mulVec_mulVec, PairStab.proj_emb]
  rw [h1]
  exact hξ

theorem crd₂_spec {c : G} (hc : c ∈ S.W₂) :
    S.C₂.E c = (slGraphAut n (ZMod 2) F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      PairStab.emb F.h (crd₂ F c) := by
  obtain ⟨η, hη⟩ := exists_emb₂ F hc
  have h1 : crd₂ F c = η := by
    rw [crd₂, hη, PairStab.graph_inv_mulVec_mulVec, PairStab.proj_emb]
  rw [h1]
  exact hη

@[expose] noncomputable def natCoord₁ : KGH91.NatCoord (Sec1216Lv.lv L (a₀ * c₀)) S.W₁ m where
  E := crd₁ F
  ρ := psi F S.lv_le_Xv
  le := fun _ hl => Sec121Swap.mem_normalizer_of_conj_mem fun _ ha => S.lv_conj_mem_W₁ hl ha
  map_mul a ha b hb := by
    rw [crd₁, crd₁, crd₁, S.C₁.map_mul a ha.1 b hb.1, Matrix.mulVec_add, PairStab.proj_add]
  inj a ha b hb h := by
    apply S.C₁.inj a ha.1 b hb.1
    rw [crd₁_spec F ha, crd₁_spec F hb, h]
  surj ξ := ⟨S.C₁.inv ((F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ PairStab.emb F.h ξ),
    S.inv_mem_W₁ (s_emb_dot F ξ), by
      rw [crd₁, S.C₁.E_inv, VecStab.inv_mulVec_mulVec, PairStab.proj_emb]⟩
  conj l a ha := by
    have h1 := psi_spec₁ F S.lv_le_Xv l ha.1
    rw [crd₁_spec F ha, frameMat_mulVec_emb] at h1
    rw [crd₁, h1, VecStab.inv_mulVec_mulVec, PairStab.proj_emb]
  ρ_surj := psi_lv_surjective F

@[expose] noncomputable def natCoord₂ : KGH91.NatCoord (Sec1216Lv.lv L (a₀ * c₀)) S.W₂ m where
  E := crd₂ F
  ρ := (slGraphAut m (ZMod 2)).toMonoidHom.comp (psi F S.lv_le_Xv)
  le := fun _ hl => Sec121Swap.mem_normalizer_of_conj_mem fun _ hc => S.lv_conj_mem_W₂ hl hc
  map_mul c hc d hd := by
    rw [crd₂, crd₂, crd₂, S.C₂.map_mul c hc.1 d hd.1, Matrix.mulVec_add, PairStab.proj_add]
  inj c hc d hd h := by
    apply S.C₂.inj c hc.1 d hd.1
    rw [crd₂_spec F hc, crd₂_spec F hd, h]
  surj η := ⟨S.C₂.inv ((slGraphAut n (ZMod 2) F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      PairStab.emb F.h η), S.inv_mem_W₂ (graph_s_emb_dot F η), by
      rw [crd₂, S.C₂.E_inv, PairStab.graph_inv_mulVec_mulVec, PairStab.proj_emb]⟩
  conj l c hc := by
    have h1 := psi_spec₂ F S.lv_le_Xv l hc.1
    rw [crd₂_spec F hc, graph_frameMat_mulVec_emb] at h1
    rw [crd₂, h1, PairStab.graph_inv_mulVec_mulVec, PairStab.proj_emb]
    rfl
  ρ_surj := (slGraphAut m (ZMod 2)).surjective.comp (psi_lv_surjective F)

theorem natCoord₂_ρ (l : ↥(Sec1216Lv.lv L (a₀ * c₀))) :
    (natCoord₂ F).ρ l = slGraphAut m (ZMod 2) ((natCoord₁ F).ρ l) := rfl

theorem isPGroup_ker_natCoord₁ : IsPGroup 2 (natCoord₁ F).ρ.ker := isPGroup_ker_psi_lv F

variable (S) in
include S in
theorem exists_swap_pair : ∃ t ∈ Subgroup.normalizer (L : Set G),
    t * a₀ * t⁻¹ = c₀ ∧ t * c₀ * t⁻¹ = a₀ ∧
      (∀ a, a ∈ V₁ ↔ t * a * t⁻¹ ∈ V₂) ∧ ∀ c, c ∈ V₂ ↔ t * c * t⁻¹ ∈ V₁ := by
  obtain ⟨m₀, hm₀, hs₁, hs₂⟩ := S.exists_swap
  have ha' : m₀ * c₀ * m₀⁻¹ ∈ V₁ := (hs₂ c₀).1 S.hc₀
  have hc' : m₀ * a₀ * m₀⁻¹ ∈ V₂ := (hs₁ a₀).1 S.ha₀
  have hne : ∀ x : G, x ≠ 1 → m₀ * x * m₀⁻¹ ≠ 1 := fun x hx h => hx (by
    calc x = m₀⁻¹ * (m₀ * x * m₀⁻¹) * m₀ := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨l, hl, hla, hlc⟩ := S.exists_pair ha' hc' S.ha₀ S.hc₀ (hne _ S.c₀_ne) (hne _ S.a₀_ne)
    S.a₀_ne S.c₀_ne (S.pairing_conj_swap hm₀ hs₁ hs₂ a₀ S.ha₀ c₀ S.hc₀)
  have ht : l * m₀ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer hl) hm₀
  have hta : l * m₀ * a₀ * (l * m₀)⁻¹ = c₀ := by
    rw [← hlc]
    group
  have htc : l * m₀ * c₀ * (l * m₀)⁻¹ = a₀ := by
    rw [← hla]
    group
  refine ⟨l * m₀, ht, hta, htc, ?_⟩
  rcases S.fix_or_swap ht with ⟨h₁, -⟩ | hsw
  · exfalso
    have h1 : c₀ ∈ V₁ ⊓ V₂ := ⟨hta ▸ (Subgroup.mem_normalizer_iff.mp h₁ a₀).mp S.ha₀, S.hc₀⟩
    rw [S.hyp.inf, Subgroup.mem_bot] at h1
    exact S.c₀_ne h1
  · exact hsw

variable (S) in
include S in
theorem mem_centralizer_of_swap {t : G} (hta : t * a₀ * t⁻¹ = c₀) (htc : t * c₀ * t⁻¹ = a₀) :
    t ∈ Subgroup.centralizer ({a₀ * c₀} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e : t * (a₀ * c₀) * t⁻¹ = a₀ * c₀ := by
    calc t * (a₀ * c₀) * t⁻¹ = (t * a₀ * t⁻¹) * (t * c₀ * t⁻¹) := by group
      _ = c₀ * a₀ := by rw [hta, htc]
      _ = a₀ * c₀ := S.comm (S.le₂ S.hc₀) (S.le₁ S.ha₀)
  calc t * (a₀ * c₀) = t * (a₀ * c₀) * t⁻¹ * t := by group
    _ = a₀ * c₀ * t := by rw [e]

theorem conj_mem_W₂ {t : G} (ht : t ∈ Subgroup.normalizer (L : Set G))
    (htc : t * c₀ * t⁻¹ = a₀) (hs₁ : ∀ a, a ∈ V₁ ↔ t * a * t⁻¹ ∈ V₂)
    (hs₂ : ∀ c, c ∈ V₂ ↔ t * c * t⁻¹ ∈ V₁) {a : G} (ha : a ∈ S.W₁) :
    t * a * t⁻¹ ∈ S.W₂ := by
  refine ⟨(hs₁ a).1 ha.1, ?_⟩
  have h1 := S.pairing_conj_swap ht hs₁ hs₂ a ha.1 c₀ S.hc₀
  rw [htc] at h1
  show KGH91.pairing S.C₁ S.C₂ a₀ (t * a * t⁻¹) = 0
  rw [h1]
  exact ha.2

variable (S) in
include S in
theorem lv_ne_bot : Sec1216Lv.lv L (a₀ * c₀) ≠ ⊥ := by
  obtain ⟨u, huW, -, hu1, -, -⟩ := S.exists_singular
  intro h
  have hu : u ∈ Sec1216Lv.lv L (a₀ * c₀) := sup_le S.W₁_le_lv S.W₂_le_lv huW
  rw [h, Subgroup.mem_bot] at hu
  exact hu1 hu

variable (S) in
include S in
theorem eq_of_lv_le {K K' : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer ({a₀ * c₀} : Set G)))
    (hK' : IsComponentIn K' (Subgroup.centralizer ({a₀ * c₀} : Set G)))
    (h₁ : Sec1216Lv.lv L (a₀ * c₀) ≤ K) (h₂ : Sec1216Lv.lv L (a₀ * c₀) ≤ K') : K = K' := by
  rcases BenderBranch.eq_or_commute_of_isComponentIn hK hK' with h | h
  · exact h
  · exfalso
    have h3 : ⁅Sec1216Lv.lv L (a₀ * c₀), Sec1216Lv.lv L (a₀ * c₀)⁆ ≤ ⁅K, K'⁆ :=
      Subgroup.commutator_mono h₁ h₂
    rw [h, Sec1216Lv.lv_perfect, le_bot_iff] at h3
    exact S.lv_ne_bot h3

variable (S) in
include S in
theorem mem_normalizer_of_lv_le {K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer ({a₀ * c₀} : Set G)))
    (hlvK : Sec1216Lv.lv L (a₀ * c₀) ≤ K) {t : G}
    (htv : t ∈ Subgroup.centralizer ({a₀ * c₀} : Set G))
    (htN : t ∈ Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G)) :
    t ∈ Subgroup.normalizer (K : Set G) := by
  have hH : (Subgroup.centralizer ({a₀ * c₀} : Set G)).map (MulAut.conj t).toMonoidHom =
      Subgroup.centralizer ({a₀ * c₀} : Set G) :=
    A38.map_conj_eq_iff.mpr (Subgroup.le_normalizer htv)
  have hK' := BenderBranch.isComponentIn_map (MulAut.conj t) hK
  rw [hH] at hK'
  have hlv' : Sec1216Lv.lv L (a₀ * c₀) ≤ K.map (MulAut.conj t).toMonoidHom := fun x hx => by
    rw [A38.mem_map_conj]
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) x).mp hx
    rw [inv_inv] at h1
    exact hlvK h1
  exact A38.map_conj_eq_iff.mp (S.eq_of_lv_le hK' hK hlv' hlvK)

theorem W_inf_centralizer {K : Subgroup G} (hlvK : Sec1216Lv.lv L (a₀ * c₀) ≤ K) :
    (S.W₁ ⊔ S.W₂) ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hwW, hwC⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup
    (fun x (hx : x ∈ S.W₁) y (hy : y ∈ S.W₂) => S.comm (S.le₁ hx.1) (S.le₂ hy.1)) hwW
  have hfix : ∀ l ∈ Sec1216Lv.lv L (a₀ * c₀), l * x * l⁻¹ = x ∧ l * y * l⁻¹ = y := by
    intro l hl
    have e : l * x * l⁻¹ * (l * y * l⁻¹) = x * y := by
      calc l * x * l⁻¹ * (l * y * l⁻¹) = l * (x * y) * l⁻¹ := by group
        _ = x * y := by
          rw [Subgroup.mem_centralizer_iff.mp hwC l (hlvK hl), mul_inv_cancel_right]
    exact S.decomp_unique (S.lv_conj_mem_W₁ hl hx).1 hx.1 (S.lv_conj_mem_W₂ hl hy).1 hy.1 e
  rw [S.eq_one_of_fixed₁ hx fun l hl => (hfix l hl).1,
    S.eq_one_of_fixed₂ hy fun l hl => (hfix l hl).2, mul_one]
  exact Subgroup.one_mem _

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
