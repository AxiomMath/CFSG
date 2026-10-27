module

public import CFSG.Quasithin.Background.G2Omega4PlusQuot
public import CFSG.Quasithin.Background.G2Omega4PlusModule

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.Om4Model
open scoped Pointwise MatrixGroups commutatorElement

variable {G : Type*} [Group G]

section FiveOfData

variable {I Sx S₂ : Subgroup G}

theorem kerSub_facts (α : ↥I →* OmG) (hα : Function.Surjective α)
    (hker : ∀ x : ↥I, α x = 1 ↔ (x : G) ∈ Sx) (hSxI : Sx ≤ I) :
    Sx ≤ kerSub I ((MonoidHom.snd _ _).comp α) ∧ Sx ≤ kerSub I ((MonoidHom.fst _ _).comp α) ∧
    kerSub I ((MonoidHom.snd _ _).comp α) ⊔ kerSub I ((MonoidHom.fst _ _).comp α) = I ∧
    kerSub I ((MonoidHom.snd _ _).comp α) ⊓ kerSub I ((MonoidHom.fst _ _).comp α) = Sx ∧
    ⁅kerSub I ((MonoidHom.snd _ _).comp α), kerSub I ((MonoidHom.fst _ _).comp α)⁆ ≤ Sx := by
  have h1 : Sx ≤ kerSub I ((MonoidHom.snd _ _).comp α) := fun x hx =>
    mem_kerSub.2 ⟨hSxI hx, by
      have := (hker ⟨x, hSxI hx⟩).2 hx
      simp [this]⟩
  have h2 : Sx ≤ kerSub I ((MonoidHom.fst _ _).comp α) := fun x hx =>
    mem_kerSub.2 ⟨hSxI hx, by
      have := (hker ⟨x, hSxI hx⟩).2 hx
      simp [this]⟩
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · apply le_antisymm
    · exact sup_le (fun x hx => (mem_kerSub.1 hx).1) (fun x hx => (mem_kerSub.1 hx).1)
    · intro x hx
      obtain ⟨m₁, hm₁⟩ := hα ((α ⟨x, hx⟩).1, 1)
      obtain ⟨m₂, hm₂⟩ := hα (1, (α ⟨x, hx⟩).2)
      have hn : α ((m₁ * m₂)⁻¹ * ⟨x, hx⟩) = 1 := by
        rw [map_mul, map_inv, map_mul, hm₁, hm₂]
        ext <;> simp
      have hnSx := (hker _).1 hn
      have hm₁M : (m₁ : G) ∈ kerSub I ((MonoidHom.snd _ _).comp α) :=
        mem_kerSub.2 ⟨m₁.2, by simp [hm₁]⟩
      have hm₂M : (m₂ : G) ∈ kerSub I ((MonoidHom.fst _ _).comp α) :=
        mem_kerSub.2 ⟨m₂.2, by simp [hm₂]⟩
      have e : x = (m₁ : G) * (m₂ : G) * (((m₁ * m₂)⁻¹ * ⟨x, hx⟩ : ↥I) : G) := by
        simp [mul_assoc]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hm₁M)
        (Subgroup.mem_sup_right hm₂M)) (Subgroup.mem_sup_left (h1 hnSx))
  · apply le_antisymm
    · intro x hx
      obtain ⟨hx₁, hx₂⟩ := hx
      obtain ⟨hxI, hq₁⟩ := mem_kerSub.1 hx₁
      obtain ⟨_, hq₂⟩ := mem_kerSub.1 hx₂
      refine (hker ⟨x, hxI⟩).1 ?_
      exact Prod.ext hq₂ hq₁
    · exact le_inf h1 h2
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨haI, ha1⟩ := mem_kerSub.1 ha
    obtain ⟨hbI, hb1⟩ := mem_kerSub.1 hb
    have hcI : ⁅a, b⁆ ∈ I := by
      rw [commutatorElement_def]
      exact I.mul_mem (I.mul_mem (I.mul_mem haI hbI) (I.inv_mem haI)) (I.inv_mem hbI)
    refine (hker ⟨⁅a, b⁆, hcI⟩).1 ?_
    have e : (⟨⁅a, b⁆, hcI⟩ : ↥I) = ⁅(⟨a, haI⟩ : ↥I), ⟨b, hbI⟩⁆ := rfl
    rw [e, map_commutatorElement]
    have e1 : α ⟨a, haI⟩ = ((α ⟨a, haI⟩).1, 1) := Prod.ext rfl ha1
    have e2 : α ⟨b, hbI⟩ = (1, (α ⟨b, hbI⟩).2) := Prod.ext hb1 rfl
    rw [e1, e2]
    ext <;> simp [commutatorElement_def]

theorem preSub_facts (Q : QuotSetting I Sx S₂) [(S₂.subgroupOf Sx).Normal]
    (Y₁ Y₂ : Subgroup (SecQuot Sx S₂))
    (hdec : ∀ y, ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, y = y₁ * y₂) (hint : ∀ y ∈ Y₁, y ∈ Y₂ → y = 1) :
    preSub Sx S₂ Y₁ ⊔ preSub Sx S₂ Y₂ = Sx ∧ preSub Sx S₂ Y₁ ⊓ preSub Sx S₂ Y₂ = S₂ ∧
    ⁅preSub Sx S₂ Y₁, preSub Sx S₂ Y₂⁆ ≤ S₂ := by
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm
    · exact sup_le (preSub_le Y₁) (preSub_le Y₂)
    · intro s hs
      obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := hdec (secMk Sx S₂ ⟨s, hs⟩)
      obtain ⟨t₁, rfl⟩ := secMk_surjective (A := Sx) (B := S₂) y₁
      obtain ⟨t₂, rfl⟩ := secMk_surjective (A := Sx) (B := S₂) y₂
      have ht₁ : (t₁ : G) ∈ preSub Sx S₂ Y₁ := mem_preSub.2 ⟨t₁.2, hy₁⟩
      have ht₂ : (t₂ : G) ∈ preSub Sx S₂ Y₂ := mem_preSub.2 ⟨t₂.2, hy₂⟩
      rw [← map_mul, secMk_eq_secMk_iff] at hy
      have hn : (s : G)⁻¹ * ((t₁ : G) * t₂) ∈ S₂ := by simpa using hy
      have e : (s : G) = (t₁ : G) * ((t₂ : G) * ((s : G)⁻¹ * ((t₁ : G) * t₂))⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht₁)
        (Subgroup.mem_sup_right (Subgroup.mul_mem _ ht₂ (Q.S₂_le_preSub Y₂ (S₂.inv_mem hn))))
  · apply le_antisymm
    · intro s hs
      obtain ⟨hs₁, hs₂⟩ := hs
      obtain ⟨hsSx, hsY₁⟩ := mem_preSub.1 hs₁
      obtain ⟨_, hsY₂⟩ := mem_preSub.1 hs₂
      exact secMk_eq_one_iff.1 (hint _ hsY₁ hsY₂)
    · exact le_inf (Q.S₂_le_preSub Y₁) (Q.S₂_le_preSub Y₂)
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    have := Q.abel a (preSub_le Y₁ ha) b (preSub_le Y₂ hb)
    simpa [commutatorElement_def] using this

theorem five_of_data [Finite G] {W U : Subgroup G} {g : G} (Q : QuotSetting I Sx S₂)
    (α : ↥I →* OmG) (hα : Function.Surjective α) (hker : ∀ x : ↥I, α x = 1 ↔ (x : G) ∈ Sx)
    (hWSx : W ≤ Sx) (hgI : g ∈ I)
    (hUc : ∀ u ∈ U, ∀ s ∈ Sx, u * s * u⁻¹ * s⁻¹ ∈ W)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, u * w * u⁻¹ * w⁻¹ ∈ S₂)
    (hSx : ∀ s ∈ Sx, ∃ w ∈ W, ∃ v ∈ W, s = w * (g⁻¹ * v * g))
    (hcap : ∀ v ∈ W, ∀ w ∈ W, w⁻¹ * (g⁻¹ * v * g) ∈ S₂ → g⁻¹ * v * g ∈ S₂)
    {τ₁ τ₂ γ₁ γ₂ : SL(2, ZMod 2)} {u₁ u₂ : ↥I}
    (hτ₁ : τ₁ * τ₁ = 1) (hτ₁' : τ₁ ≠ 1) (hτ₂ : τ₂ * τ₂ = 1) (hτ₂' : τ₂ ≠ 1)
    (hγ₁ : γ₁ ^ 3 = 1) (hγ₁' : γ₁ ≠ 1) (hγ₂ : γ₂ ^ 3 = 1) (hγ₂' : γ₂ ≠ 1)
    (hu₁ : (u₁ : G) ∈ U) (hα₁ : α u₁ = (τ₁, 1)) (hu₂ : (u₂ : G) ∈ U) (hα₂ : α u₂ = (1, τ₂))
    (hαg : α ⟨g, hgI⟩ = (γ₁, γ₂)) :
    ∃ M₁ M₂ Sa Sb : Subgroup G,
      Sx ≤ M₁ ∧ Sx ≤ M₂ ∧ M₁ ≤ I ∧ M₂ ≤ I ∧ M₁ ⊔ M₂ = I ∧ M₁ ⊓ M₂ = Sx ∧ ⁅M₁, M₂⁆ ≤ Sx ∧
      S₂ ≤ Sa ∧ Sa ≤ Sx ∧ S₂ ≤ Sb ∧ Sb ≤ Sx ∧ Sa ⊔ Sb = Sx ∧ Sa ⊓ Sb = S₂ ∧ ⁅Sa, Sb⁆ ≤ S₂ ∧
      Sa = ⁅Sx, M₁⁆ ⊔ S₂ ∧ Sb = ⁅Sx, M₂⁆ ⊔ S₂ ∧
      (∀ s ∈ Sx, s ∈ Sa ↔ ∀ m ∈ M₂, ⁅m, s⁆ ∈ S₂) ∧
      (∀ s ∈ Sx, s ∈ Sb ↔ ∀ m ∈ M₁, ⁅m, s⁆ ∈ S₂) ∧
      IsSumOfNaturalSL2Modules M₁ Sa Sx S₂ ∧ IsSumOfNaturalSL2Modules M₂ Sb Sx S₂ := by
  have hN := Q.normal
  let hCG : CommGroup (SecQuot Sx S₂) := Q.quotCommGroup
  have hker' : α.ker ≤ Q.convAct.ker := by
    intro x hx
    exact (MonoidHom.mem_ker).2 (Q.convAct_ker x ((hker x).1 hx))
  obtain ⟨ρ, hρ⟩ : ∃ ρ : OmG →* MulAut (SecQuot Sx S₂), ∀ x : ↥I, ρ (α x) = Q.convAct x :=
    ⟨α.liftOfRightInverse (Function.surjInv hα) (Function.rightInverse_surjInv hα)
      ⟨Q.convAct, hker'⟩, fun x => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x⟩
  have hρ₁ : ρ (τ₁, 1) = Q.convAct u₁ := by rw [← hα₁, hρ]
  have hρ₂ : ρ (1, τ₂) = Q.convAct u₂ := by rw [← hα₂, hρ]
  have hgSx : ∀ v ∈ Sx, g⁻¹ * v * g ∈ Sx := fun v hv => by
    simpa using Q.nS g⁻¹ (inv_mem hgI) v hv
  have hρg : ∀ (v : G) (hv : v ∈ Sx), ρ (γ₁, γ₂)⁻¹ (secMk Sx S₂ ⟨v, hv⟩) =
      secMk Sx S₂ ⟨g⁻¹ * v * g, hgSx v hv⟩ := by
    intro v hv
    have h1 : ρ (γ₁, γ₂)⁻¹ = Q.convAct ((⟨g, hgI⟩ : ↥I)⁻¹) := by
      rw [← hαg, ← map_inv, hρ]
    rw [h1, Q.convAct_mk]
    congr 1
    apply Subtype.ext
    simp
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Subgroup (SecQuot Sx S₂),
      ∀ y, y ∈ W₀ ↔ ∃ x : ↥Sx, (x : G) ∈ W ∧ secMk Sx S₂ x = y :=
    ⟨(W.subgroupOf Sx).map (secMk Sx S₂), fun y => by
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]⟩
  have hy2 : ∀ y : SecQuot Sx S₂, y⁻¹ = y := fun y => inv_eq_of_mul_eq_one_right (Q.quot_sq y)
  have hq : ∀ u : ↥I, (u : G) ∈ U → ∀ y : SecQuot Sx S₂, Q.convAct u y * y ∈ W₀ := by
    intro u hu y
    obtain ⟨s, rfl⟩ := secMk_surjective (A := Sx) (B := S₂) y
    have hc : (u : G) * s * (u : G)⁻¹ * (s : G)⁻¹ ∈ Sx :=
      Sx.mul_mem (Q.nS u u.2 s s.2) (inv_mem s.2)
    refine (hW₀ _).2 ⟨⟨_, hc⟩, hUc u hu s s.2, ?_⟩
    have e : (⟨(u : G) * s * (u : G)⁻¹ * (s : G)⁻¹, hc⟩ : ↥Sx) =
        ⟨(u : G) * s * (u : G)⁻¹, Q.nS u u.2 s s.2⟩ * s⁻¹ := rfl
    rw [e, map_mul, map_inv, hy2, Q.convAct_mk]
  have hf : ∀ u : ↥I, (u : G) ∈ U → ∀ w ∈ W₀, Q.convAct u w = w := by
    intro u hu w hw
    obtain ⟨x, hxW, rfl⟩ := (hW₀ w).1 hw
    rw [Q.convAct_mk, secMk_eq_secMk_iff]
    have h := hUW u hu _ (W.inv_mem hxW)
    show ((u : G) * x * (u : G)⁻¹)⁻¹ * x ∈ S₂
    have e : ((u : G) * x * (u : G)⁻¹)⁻¹ * x =
        (u : G) * (x : G)⁻¹ * (u : G)⁻¹ * ((x : G)⁻¹)⁻¹ := by group
    rw [e]
    exact h
  have hsum : ∀ y : SecQuot Sx S₂, ∃ w₀ ∈ W₀, ∃ w₁ ∈ W₀, y = w₀ * ρ (γ₁, γ₂)⁻¹ w₁ := by
    intro y
    obtain ⟨s, rfl⟩ := secMk_surjective (A := Sx) (B := S₂) y
    obtain ⟨w, hw, v, hv, hs⟩ := hSx s s.2
    have hwS : w ∈ Sx := hWSx hw
    have hvS : v ∈ Sx := hWSx hv
    refine ⟨secMk Sx S₂ ⟨w, hwS⟩, (hW₀ _).2 ⟨⟨w, hwS⟩, hw, rfl⟩, secMk Sx S₂ ⟨v, hvS⟩,
      (hW₀ _).2 ⟨⟨v, hvS⟩, hv, rfl⟩, ?_⟩
    rw [hρg v hvS, ← map_mul]
    congr 1
    exact Subtype.ext hs
  have hcap' : ∀ w₁ ∈ W₀, ρ (γ₁, γ₂)⁻¹ w₁ ∈ W₀ → ρ (γ₁, γ₂)⁻¹ w₁ = 1 := by
    intro w₁ hw₁ hmem
    obtain ⟨x, hxW, rfl⟩ := (hW₀ w₁).1 hw₁
    have e : ρ (γ₁, γ₂)⁻¹ (secMk Sx S₂ x) = secMk Sx S₂ ⟨g⁻¹ * (x : G) * g, hgSx x x.2⟩ :=
      hρg x x.2
    rw [e] at hmem ⊢
    obtain ⟨x', hx'W, hx'⟩ := (hW₀ _).1 hmem
    rw [secMk_eq_secMk_iff] at hx'
    exact secMk_eq_one_iff.2 (hcap x hxW x' hx'W hx')
  obtain ⟨Y₁, Y₂, hdec, hint, -, -, hiff₁, hiff₂, hcl₁, hcl₂, hnat₁, hnat₂⟩ :=
    mul_module_decomposition (Y := SecQuot Sx S₂) Q.quot_sq ρ hτ₁ hτ₁' hτ₂ hτ₂' hγ₁ hγ₁' hγ₂ hγ₂'
      (fun y => by rw [hρ₁]; exact hq u₁ hu₁ y) (fun y => by rw [hρ₂]; exact hq u₂ hu₂ y)
      (fun w hw => by rw [hρ₁]; exact hf u₁ hu₁ w hw)
      (fun w hw => by rw [hρ₂]; exact hf u₂ hu₂ w hw) hsum hcap'
  obtain ⟨h1, h2, h3, h4, h5⟩ := kerSub_facts α hα hker Q.Sx_le
  obtain ⟨h6, h7, h8⟩ := preSub_facts Q Y₁ Y₂ hdec hint
  have D₁ : HalfData Q ((MonoidHom.fst _ _).comp α) ((MonoidHom.snd _ _).comp α)
      (ρ.comp (MonoidHom.inl _ _)) (ρ.comp (MonoidHom.inr _ _)) Y₁ :=
    { surj := fun A => by
        obtain ⟨m, hm⟩ := hα (A, 1)
        exact ⟨m, by simp [hm], by simp [hm]⟩
      surj' := fun B => by
        obtain ⟨m, hm⟩ := hα (1, B)
        exact ⟨m, by simp [hm], by simp [hm]⟩
      ker := fun m => by
        rw [← hker m]
        exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩
      relA := fun m hm => by
        rw [← hρ m]
        show ρ (α m) = ρ ((α m).1, 1)
        congr 1
        exact Prod.ext rfl hm
      relB := fun m hm => by
        rw [← hρ m]
        show ρ (α m) = ρ (1, (α m).2)
        congr 1
        exact Prod.ext hm rfl
      iff := hiff₁
      cl := hcl₁
      nat := hnat₁ }
  have D₂ : HalfData Q ((MonoidHom.snd _ _).comp α) ((MonoidHom.fst _ _).comp α)
      (ρ.comp (MonoidHom.inr _ _)) (ρ.comp (MonoidHom.inl _ _)) Y₂ :=
    { surj := fun A => by
        obtain ⟨m, hm⟩ := hα (1, A)
        exact ⟨m, by simp [hm], by simp [hm]⟩
      surj' := fun B => by
        obtain ⟨m, hm⟩ := hα (B, 1)
        exact ⟨m, by simp [hm], by simp [hm]⟩
      ker := fun m => by
        rw [← hker m]
        exact ⟨fun h => Prod.ext h.2 h.1, fun h => ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩⟩
      relA := fun m hm => by
        rw [← hρ m]
        show ρ (α m) = ρ (1, (α m).2)
        congr 1
        exact Prod.ext hm rfl
      relB := fun m hm => by
        rw [← hρ m]
        show ρ (α m) = ρ ((α m).1, 1)
        congr 1
        exact Prod.ext rfl hm
      iff := hiff₂
      cl := hcl₂
      nat := hnat₂ }
  exact ⟨kerSub I ((MonoidHom.snd _ _).comp α), kerSub I ((MonoidHom.fst _ _).comp α),
    preSub Sx S₂ Y₁, preSub Sx S₂ Y₂, h1, h2, fun x hx => (mem_kerSub.1 hx).1,
    fun x hx => (mem_kerSub.1 hx).1, h3, h4, h5, Q.S₂_le_preSub Y₁, preSub_le Y₁,
    Q.S₂_le_preSub Y₂, preSub_le Y₂, h6, h7, h8, D₁.eq_comm_sup, D₂.eq_comm_sup,
    fun s hs => D₁.mem_iff_comm hs, fun s hs => D₂.mem_iff_comm hs, D₁.natural, D₂.natural⟩

end FiveOfData

end CFSG.Quasithin
