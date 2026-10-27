module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep7C

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

section Env

variable {T L V V₁ V₂ K₁ : Subgroup G} {g : G} {D : HatModelU (u128 V V₁)}

theorem DIEnv.kap_stab_fl (E : DIEnv T L V V₁ V₂ K₁ g D) {k : G} (hkK : k ∈ K₁)
    (hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G))
    (hρ : D.ρ ⟨k, hkN⟩ (D.π E.a) = D.π E.a) (v : Additive ↥E.I) :
    v ∈ E.fl ↔ E.kap ⟨D.ρ ⟨k, hkN⟩, L128A.HatU.rho_mem_img D hkK hkN⟩ v ∈ E.fl := by
  have hmem : E.kap ⟨D.ρ ⟨k, hkN⟩, L128A.HatU.rho_mem_img D hkK hkN⟩ ∈
      kmapOf (D.img K₁) E.kap (stabS (Submodule.span (ZMod 2) {D.π E.a})) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (mem_stabS_span_of_fix hρ))
  rw [E.hY₁] at hmem
  exact mem_stabS_iff.1 hmem v

theorem k0_inv_rho (E : DIEnv T L V V₁ V₂ K₁ g D) {k : G}
    (hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G))
    (hρ : D.ρ ⟨k, hkN⟩ (D.π E.a) = D.π E.a) :
    D.ρ ⟨k⁻¹, Subgroup.inv_mem _ hkN⟩ (D.π E.a) = D.π E.a := by
  have e : D.ρ ⟨k⁻¹, Subgroup.inv_mem _ hkN⟩ = (D.ρ ⟨k, hkN⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e]
  show (D.ρ ⟨k, hkN⟩).symm (D.π E.a) = D.π E.a
  rw [LinearEquiv.symm_apply_eq]
  exact hρ.symm

theorem DIEnv.mem_DI_iff (E : DIEnv T L V V₁ V₂ K₁ g D)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W)
    (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) (F2 : FactF2) (F3 : FactF3)
        (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp) {x : G} (hx : x ∈ E.I) :
    x ∈ E.I ⊓ wcSub T L V V₁ ↔ (Additive.ofMul ⟨x, hx⟩ : Additive ↥E.I) ∈ E.fl := by
  constructor
  · intro h
    exact (E.point_fix h1222 h12213 h1289 h12810 h12813 F2 F3 hpt x hx).1 (Subgroup.mem_inf.1 h).2
  · intro h
    exact Subgroup.mem_inf.2 ⟨hx, (E.point_fix h1222 h12213 h1289 h12810 h12813 F2 F3 hpt x hx).2 h⟩

theorem DIEnv.K0_norm_DI (E : DIEnv T L V V₁ V₂ K₁ g D)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W)
    (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) (F2 : FactF2) (F3 : FactF3)
        (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp) {k : G} (hkK : k ∈ K₁)
    (hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G))
    (hρ : D.ρ ⟨k, hkN⟩ (D.π E.a) = D.π E.a) {x : G} (hx : x ∈ E.I ⊓ wcSub T L V V₁) :
    k * x * k⁻¹ ∈ E.I ⊓ wcSub T L V V₁ := by
  obtain ⟨hxI, hxW⟩ := Subgroup.mem_inf.1 hx
  have hkxI : k * x * k⁻¹ ∈ E.I := (Subgroup.mem_normalizer_iff.1 (E.hKI hkK) x).1 hxI
  have hxf : (Additive.ofMul ⟨x, hxI⟩ : Additive ↥E.I) ∈ E.fl :=
    (E.mem_DI_iff h1222 h12213 h1289 h12810 h12813 F2 F3 hpt hxI).1 hx
  have hstab := E.kap_stab_fl hkK hkN hρ (Additive.ofMul ⟨x, hxI⟩)
  have hact := E.action hkN (E.hKI hkK) (E.hK₁H hkK) (L128A.HatU.rho_mem_img D hkK hkN)
    (Additive.ofMul ⟨x, hxI⟩)
  have e : (Additive.ofMul ⟨k * x * k⁻¹, hkxI⟩ : Additive ↥E.I) =
      E.kap ⟨D.ρ ⟨k, hkN⟩, L128A.HatU.rho_mem_img D hkK hkN⟩ (Additive.ofMul ⟨x, hxI⟩) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hact.symm
  have hf' : (Additive.ofMul ⟨k * x * k⁻¹, hkxI⟩ : Additive ↥E.I) ∈ E.fl := by
    rw [e]
    exact hstab.1 hxf
  exact (E.mem_DI_iff h1222 h12213 h1289 h12810 h12813 F2 F3 hpt hkxI).2 hf'

theorem DIEnv.K0_normalizes_DI (E : DIEnv T L V V₁ V₂ K₁ g D)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W)
    (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) (F2 : FactF2) (F3 : FactF3)
        (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp) {k : G} (hkK : k ∈ K₁)
    (hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G))
    (hρ : D.ρ ⟨k, hkN⟩ (D.π E.a) = D.π E.a) :
    k ∈ Subgroup.normalizer ((E.I ⊓ wcSub T L V V₁ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => E.K0_norm_DI h1222 h12213 h1289 h12810 h12813 F2 F3 hpt hkK hkN hρ hx
  · intro hx
    have h := E.K0_norm_DI h1222 h12213 h1289 h12810 h12813 F2 F3 hpt
      (Subgroup.inv_mem _ hkK) (Subgroup.inv_mem _ hkN) (k0_inv_rho E hkN hρ) hx
    simpa [mul_assoc] using h

theorem DIEnv.card_DI (E : DIEnv T L V V₁ V₂ K₁ g D)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W)
    (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) (F2 : FactF2) (F3 : FactF3)
        (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp) :
    Nat.card ↥(E.I ⊓ wcSub T L V V₁) = 4 := by
  rw [natCard_inf_eq_submodule E.fl (fun i hi => E.point_fix h1222 h12213 h1289 h12810 h12813 F2
    F3 hpt i hi), natCard_submodule_two, E.hℓ]
  norm_num

end Env

end CFSG.Quasithin.H13.C1294
