module

public import CFSG.Quasithin.Vol2.Ch10SecC8Data
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5VecAux
public import CFSG.Quasithin.Vol2.Ch10SecE9N

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def e0 : L3.Vec := ![1, 0, 0]

theorem fix_U3 : ∀ w : L3.Vec, (∀ u : L32.Γ, L32.IsU u → L3.act u w = w) → w = 0 ∨ w = e0 := by
  unfold L32.IsU L32.ent L3.act e0
  decide +kernel

theorem act_pa_e0 : ∀ g : L32.Γ, L32.IsPa g → L3.act g e0 = e0 := by
  unfold L32.IsPa L32.ent L3.act e0
  decide +kernel

theorem exists_pa_three : ∃ g : L32.Γ, L32.IsPa g ∧ g ^ 3 = 1 ∧ g ≠ 1 := by
  unfold L32.IsPa L32.ent
  decide +kernel

end CFSG.Quasithin.Vol2.Ch10.SecB.E9

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

@[expose] def PtCond (T L I P : Subgroup G) : Prop :=
  ∀ x ∈ oTwoUpper P, ∀ v ∈ fsuUL T L I,
    (∀ s ∈ T1 T L, s * v * s⁻¹ * v⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G)) →
    x * v * x⁻¹ * v⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G)

variable {T L I : Subgroup G} {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ}

theorem exists_mul_of_mem_fsuL0 (h : MaxCtx T L I t Ψ c) {x : G} (hx : x ∈ fsuL0 T L) :
    ∃ l ∈ L, ∃ l' ∈ CFSG.conjugate L t, l * l' = x := by
  rw [SecA.fsuL0_eq_sup h.h37 h.h38 h.hyp h.ht h.htn] at hx
  have h' : x ∈ ((L ⊔ CFSG.conjugate L t : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L (CFSG.conjugate L t)
    (SecC.conjugate_le_normalizer h.hyp h.ht)] at h'
  obtain ⟨l, hl, l', hl', hll'⟩ := Set.mem_mul.mp h'
  exact ⟨l, hl, l', hl', hll'⟩

theorem exists_mem_L_fst (h : MaxCtx T L I t Ψ c) (a : L32.Γ) :
    ∃ (l : G) (hl : l ∈ L), Ψ ⟨l, SecA.le_fsuL0 T L hl⟩ = (a, 1) := by
  obtain ⟨⟨y, hy⟩, hya⟩ := h.hC.surj (a, 1)
  obtain ⟨l, hl, l', hl', rfl⟩ := exists_mul_of_mem_fsuL0 h hy
  refine ⟨l, hl, ?_⟩
  have e : (⟨l * l', hy⟩ : ↥(fsuL0 T L)) =
      ⟨l, SecA.le_fsuL0 T L hl⟩ * ⟨l', SecA.conjugate_le_fsuL0 h.ht hl'⟩ := rfl
  rw [e, map_mul] at hya
  have h1 := h.hC.onL l (SecA.le_fsuL0 T L hl) hl
  have h2 := h.hC.onLt l' (SecA.conjugate_le_fsuL0 h.ht hl') hl'
  refine Prod.ext ?_ h1
  have := congrArg Prod.fst hya
  rw [Prod.fst_mul, h2, mul_one] at this
  exact this

theorem exists_ptCond (h : MaxCtx T L I t Ψ c) (h3 : Case10_1_1Three T L I)
    (h1011 : Stmt10_1_1) (h322 : TmpL6_3_2_2_two) :
    ∃ A : Subgroup L32.Γ, (A = L32.Pa ∨ A = L32.Pb) ∧ PtCond T L I (preIn Ψ (A.prod A) ⊔ T) := by
  obtain ⟨hcU, hnat⟩ := h3.2
  obtain ⟨D0⟩ := hnat.toL3Coord
  obtain ⟨D, hD⟩ := SecC.exists_L3Data_U3 h.hyp D0
  have hLV := SecC.le_normalizer_fsuUL T L I
  set ρ := InternalSec.autOnHom hLV with hρ
  let eπ : L3.Γ ≃* ↥(autOn L (fsuUL T L I)) :=
    MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩
  let γ : ↥L →* L32.Γ := eπ.symm.toMonoidHom.comp ρ
  have hγπ : ∀ l : ↥L, D.π (γ l) = ρ l := fun l => eπ.apply_symm_apply (ρ l)
  have hγs : Function.Surjective γ := eπ.symm.surjective.comp (InternalSec.autOnHom_surjective hLV)
  have hρv : ∀ (l : ↥L) (v : ↥(fsuUL T L I)),
      ((((ρ l : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) v : ↥(fsuUL T L I)) : G) =
        (l : G) * v * (l : G)⁻¹ := fun l v => Setup.rho_apply_coe hLV l v
  let b : ↥(fsuUL T L I) → L3.Vec := fun v => Multiplicative.toAdd (D.β ⟨v, Subgroup.mem_top v⟩)
  have hb : ∀ (l : ↥L) (v : ↥(fsuUL T L I)) (hv : (l : G) * v * (l : G)⁻¹ ∈ fsuUL T L I),
      b ⟨(l : G) * v * (l : G)⁻¹, hv⟩ = L3.act (γ l) (b v) := by
    intro l v hv
    have hu : ((D.π (γ l) : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I))
        ((⟨v, Subgroup.mem_top v⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) : ↥(fsuUL T L I)) ∈
        (⊤ : Subgroup ↥(fsuUL T L I)) := Subgroup.mem_top _
    have h1 := D.equi (γ l) ⟨v, Subgroup.mem_top v⟩ hu
    have e : (⟨⟨(l : G) * v * (l : G)⁻¹, hv⟩, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I)))
        = ⟨((D.π (γ l) : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) v, hu⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hγπ]
      exact (hρv l v).symm
    show Multiplicative.toAdd (D.β ⟨⟨(l : G) * v * (l : G)⁻¹, hv⟩, Subgroup.mem_top _⟩) = _
    rw [e, h1]
    rfl
  have hb0 : ∀ v : ↥(fsuUL T L I),
      b v = 0 ↔ (v : G) ∈ Subgroup.centralizer (fsuL0 T L : Set G) := by
    intro v
    rw [← Subgroup.mem_subgroupOf]
    rw [← D.ker_β ⟨v, Subgroup.mem_top v⟩]
    exact toAdd_eq_zero
  have hbmul : ∀ v w : ↥(fsuUL T L I), b (v * w) = b v + b w := fun v w => by
    show Multiplicative.toAdd (D.β ⟨v * w, _⟩) = _
    rw [show (⟨v * w, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) =
      ⟨v, Subgroup.mem_top v⟩ * ⟨w, Subgroup.mem_top w⟩ from rfl, map_mul, toAdd_mul]
  have hbinv : ∀ v : ↥(fsuUL T L I), b v⁻¹ = - b v := fun v => by
    show Multiplicative.toAdd (D.β ⟨v⁻¹, _⟩) = _
    rw [show (⟨v⁻¹, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) =
      (⟨v, Subgroup.mem_top v⟩)⁻¹ from rfl, map_inv, toAdd_inv]
  have hfixU : ∀ v : ↥(fsuUL T L I),
      (∀ s ∈ T1 T L, s * v * s⁻¹ * (v : G)⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G)) →
      ∀ u : L32.Γ, L32.IsU u → L3.act u (b v) = b v := by
    intro v hvT u hu
    have hu' : ((D.π u : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) ∈
        autOn (T ⊓ L) (fsuUL T L I) := (hD u).mpr hu
    obtain ⟨g, hgTL, hg⟩ := Setup.mem_autOn_iff.mp hu'
    have hgL : (g : G) ∈ L := hgTL.2
    have hγg : γ ⟨g, hgL⟩ = u := by
      apply D.π_injective
      rw [hγπ]
      apply Subtype.ext
      rw [← hg]
      rfl
    have hgv : (g : G) * v * (g : G)⁻¹ ∈ fsuUL T L I :=
      (Subgroup.mem_normalizer_iff.mp (hLV hgL) v).mp v.2
    have h1 := hb ⟨g, hgL⟩ v hgv
    rw [hγg] at h1
    rw [← h1]
    have h2 : (g : G) * v * (g : G)⁻¹ * (v : G)⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G) :=
      hvT g ⟨hgTL.1, Subgroup.le_normalizer hgL⟩
    have h3 : b (⟨(g : G) * v * (g : G)⁻¹, hgv⟩ * v⁻¹) = 0 := (hb0 _).mpr h2
    rw [hbmul, hbinv] at h3
    exact add_neg_eq_zero.mp h3
  let ψ : ↥L →* L32.Γ :=
    (MonoidHom.fst _ _).comp (Ψ.comp (Subgroup.inclusion (SecA.le_fsuL0 T L)))
  have hψ : ∀ l : ↥L, ψ l = (Ψ ⟨l, SecA.le_fsuL0 T L l.2⟩).1 := fun l => rfl
  have hψker : ∀ l : ↥L, ψ l = 1 → (l : G) ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
    intro l hl
    have h1 : Ψ ⟨l, SecA.le_fsuL0 T L l.2⟩ = 1 :=
      Prod.ext hl (h.hC.onL l (SecA.le_fsuL0 T L l.2) l.2)
    exact SecA.pCoreOf_fsuL0_le_centralizer h322 h.hyp ((h.hC.ker _).mp h1)
  have hψγ : ∀ l : ↥L, ψ l = 1 → γ l = 1 := by
    intro l hl
    have h1 : l ∈ ρ.ker := by
      rw [InternalSec.mem_ker_autOnHom]
      exact Subgroup.centralizer_le (SecA.fsuUL_le_fsuVM T L I) (hψker l hl)
    show eπ.symm (ρ l) = 1
    rw [MonoidHom.mem_ker.mp h1, map_one]
  obtain ⟨_, -, -, hthree, -⟩ := h.hyp.three
  have hLtV : ∀ l' ∈ CFSG.conjugate L t, ∀ v ∈ fsuUL T L I, l' * v * l'⁻¹ = v := by
    intro l' hl' v hv
    have h1 := Subgroup.mem_centralizer_iff.mp ((hthree t h.ht h.htn).2.2 hv) l' hl'
    rw [h1, mul_inv_cancel_right]
  have hρeq : ∀ l d : ↥L, (∀ v ∈ fsuUL T L I, (l : G) * v * (l : G)⁻¹ = d * v * (d : G)⁻¹) →
      γ l = γ d := by
    intro l d hld
    show eπ.symm (ρ l) = eπ.symm (ρ d)
    congr 1
    apply Subtype.ext
    ext v
    rw [hρv, hρv]
    exact hld v v.2
  set S : Subgroup ↥L := L32.Pa.comap γ with hS
  have hU3B : L32.U3 ≤ S.map ψ := by
    intro u hu
    have hmem : (u, (1 : L32.Γ)) ∈ ((T0 T L).subgroupOf (fsuL0 T L)).map Ψ := by
      rw [h.hC.T0]
      exact ⟨hu, L32.U3.one_mem⟩
    obtain ⟨⟨x, hxL0⟩, hxT0, hxu⟩ := hmem
    have hxT0' : x ∈ T0 T L := Subgroup.mem_subgroupOf.mp hxT0
    obtain ⟨l, hl, l', hl', rfl⟩ := exists_mul_of_mem_fsuL0 h hxL0
    have hΨ : Ψ ⟨l * l', hxL0⟩ =
        Ψ ⟨l, SecA.le_fsuL0 T L hl⟩ * Ψ ⟨l', SecA.conjugate_le_fsuL0 h.ht hl'⟩ := by
      rw [← map_mul]
      rfl
    have hψl : ψ ⟨l, hl⟩ = u := by
      rw [hψ]
      have h1 := congrArg Prod.fst hxu
      rw [hΨ, Prod.fst_mul, h.hC.onLt l' _ hl', mul_one] at h1
      exact h1
    have hxN : l * l' ∈ Subgroup.normalizer (L : Set G) :=
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (SecA.le_fsuL0 T L)).mp
        (SecA.normal_fsuL0 h.hyp.fsu.maximal.1)) hxL0
    obtain ⟨d, hd, hdv⟩ := SecC.exists_mem_inf_acts_fsuUL h.hyp h1011 h3 D hD ⟨hxT0'.1, hxN⟩
    have hγld : γ ⟨l, hl⟩ = γ ⟨d, hd.2⟩ := by
      apply hρeq
      intro v hv
      rw [← hdv v hv, show l * l' * v * (l * l')⁻¹ = l * (l' * v * l'⁻¹) * l⁻¹ by group,
        hLtV l' hl' v hv]
    have hγd : γ ⟨d, hd.2⟩ ∈ L32.U3 := by
      apply (hD _).mp
      rw [hγπ]
      exact Setup.mem_autOn_iff.mpr ⟨⟨d, hLV hd.2⟩, hd, rfl⟩
    exact ⟨⟨l, hl⟩, (show γ ⟨l, hl⟩ ∈ L32.Pa from hγld ▸ parData_a.uA hγd), hψl⟩
  have hBtop : S.map ψ ≠ ⊤ := by
    intro htop
    apply pa_ne_top
    rw [eq_top_iff]
    intro g _
    obtain ⟨l₀, rfl⟩ := hγs g
    have hl₀ : ψ l₀ ∈ S.map ψ := by rw [htop]; trivial
    obtain ⟨s, hsS, hs⟩ := hl₀
    have h1 : γ (s⁻¹ * l₀) = 1 := hψγ _ (by rw [map_mul, map_inv, hs, inv_mul_cancel])
    have h2 : γ l₀ = γ s := by
      rw [map_mul, map_inv] at h1
      exact (inv_mul_eq_one.mp h1).symm
    rw [h2]
    exact hsS
  have hBU3 : S.map ψ ≠ L32.U3 := by
    intro hU
    obtain ⟨g, hgPa, hg3, hg1⟩ := E9.exists_pa_three
    obtain ⟨l, rfl⟩ := hγs g
    have hlS : l ∈ S := hgPa
    have h1 : ψ l ∈ L32.U3 := hU ▸ ⟨l, hlS, rfl⟩
    have h2 : ψ (l ^ 8) = 1 := by rw [map_pow]; exact E9.isU_pow_eight _ h1
    have h3 : γ l ^ 8 = 1 := by rw [← map_pow]; exact hψγ _ h2
    apply hg1
    calc γ l = (γ l ^ 3) ^ 3 * (γ l ^ 8)⁻¹ := by group
      _ = 1 := by rw [h3, hg3, one_pow, inv_one, mul_one]
  have hA : S.map ψ = L32.Pa ∨ S.map ψ = L32.Pb := by
    rcases L32.overgroups _ hU3B with h1 | h1 | h1 | h1
    · exact absurd h1 hBU3
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 hBtop
  refine ⟨S.map ψ, hA, ?_⟩
  intro x hx v hv hvT
  obtain ⟨K, E, hDA⟩ : ∃ K E : Subgroup L32.Γ, ParData (S.map ψ) K E := by
    rcases hA with h1 | h1
    · exact ⟨_, _, h1 ▸ parData_a⟩
    · exact ⟨_, _, h1 ▸ parData_b⟩
  have hxL0 := XOf_le_fsuL0 h hDA hx
  have hxK := mem_prod_of_mem_XOf h hDA hx
  obtain ⟨s, hsS, hsx⟩ := hDA.KA hxK.1
  obtain ⟨l, hl, l', hl', rfl⟩ := exists_mul_of_mem_fsuL0 h hxL0
  have hΨ : Ψ ⟨l * l', hxL0⟩ =
      Ψ ⟨l, SecA.le_fsuL0 T L hl⟩ * Ψ ⟨l', SecA.conjugate_le_fsuL0 h.ht hl'⟩ := by
    rw [← map_mul]
    rfl
  have hψl : ψ ⟨l, hl⟩ = (Ψ ⟨l * l', hxL0⟩).1 := by
    rw [hψ, hΨ, Prod.fst_mul, h.hC.onLt l' _ hl', mul_one]
  have hsl : ψ (s⁻¹ * ⟨l, hl⟩) = 1 := by rw [map_mul, map_inv, hsx, hψl, inv_mul_cancel]
  have hc' := hψker _ hsl
  have hvV : v ∈ fsuVM T L I := SecA.fsuUL_le_fsuVM T L I hv
  have hcv := Subgroup.mem_centralizer_iff.mp hc' v hvV
  have hact : l * l' * v * (l * l')⁻¹ = s * v * (s : G)⁻¹ := by
    rw [show l * l' * v * (l * l')⁻¹ = l * (l' * v * l'⁻¹) * l⁻¹ by group, hLtV l' hl' v hv]
    have e : l = s * ((s : G)⁻¹ * l) := by group
    rw [e, show (s : G) * ((s : G)⁻¹ * l) * v * ((s : G) * ((s : G)⁻¹ * l))⁻¹ =
      s * (((s : G)⁻¹ * l) * v) * ((s : G)⁻¹ * l)⁻¹ * (s : G)⁻¹ by group]
    have hcv' : ((s : G)⁻¹ * l) * v = v * ((s : G)⁻¹ * l) := by
      have := hcv
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      exact this.symm
    rw [hcv']
    group
  rw [hact]
  have hsv : (s : G) * v * (s : G)⁻¹ ∈ fsuUL T L I :=
    (Subgroup.mem_normalizer_iff.mp (hLV s.2) v).mp hv
  have hfix := hfixU ⟨v, hv⟩ hvT
  have hγs' : L3.act (γ s) (b ⟨v, hv⟩) = b ⟨v, hv⟩ := by
    rcases E9.fix_U3 _ hfix with h0 | h0
    · rw [h0, L3.act_zero]
    · rw [h0]
      exact E9.act_pa_e0 _ hsS
  have h1 := hb s ⟨v, hv⟩ hsv
  rw [hγs'] at h1
  have h2 : b (⟨(s : G) * v * (s : G)⁻¹, hsv⟩ * (⟨v, hv⟩ : ↥(fsuUL T L I))⁻¹) = 0 := by
    rw [hbmul, hbinv, h1]
    exact add_neg_cancel _
  exact (hb0 _).mp h2

end CFSG.Quasithin.Vol2.Ch10.SecB
