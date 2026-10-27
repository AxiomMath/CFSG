module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNe
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNd
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN3

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.Quasithin
open Module
open scoped commutatorElement

section Kappa

variable {G : Type} [Group G] {Λ Lu V W₀ W₁ : Subgroup G} {M : Type} [AddCommGroup M]
  [Module (ZMod 2) M] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

private abbrev toM2_LNe2 (a : Multiplicative M) : M := Additive.ofMul a

private abbrev toW2_LNe2 (a : Multiplicative W) : W := Additive.ofMul a

private lemma toM2_mul_LNe2 (a b : Multiplicative M) :
    toM2_LNe2 (a * b) = toM2_LNe2 a + toM2_LNe2 b := rfl

private lemma toW2_mul_LNe2 (a b : Multiplicative W) :
    toW2_LNe2 (a * b) = toW2_LNe2 a + toW2_LNe2 b := rfl

private lemma toW2_one_LNe2 : toW2_LNe2 (1 : Multiplicative W) = 0 := rfl

private def psiLNe2 (SM : SectionModule Lu ⊥ V M) {K : Subgroup G} (hK : K ≤ V) :
    ↥K →* Multiplicative M :=
  SM.π.comp (Subgroup.inclusion hK)

private lemma psiLNe2_injective (SM : SectionModule Lu ⊥ V M) {K : Subgroup G} (hK : K ≤ V) :
    Function.Injective (psiLNe2 SM hK) :=
  (SM.π_injective_of_bot rfl).comp (Subgroup.inclusion_injective hK)

private def phiLNe2 (SW : SectionModule Λ W₀ W₁ W) {K : Subgroup G} (hKW : K ≤ W₁) :
    ↥K →* Multiplicative W :=
  SW.π.comp (Subgroup.inclusion hKW)

private noncomputable def pickLNe2 (SM : SectionModule Lu ⊥ V M) {K : Subgroup G}
    (m : ↥(SM.sub K)) : ↥K :=
  ⟨(Classical.choose (SM.mem_sub.mp m.2)).1, (Classical.choose_spec (SM.mem_sub.mp m.2)).1⟩

private lemma psi_pickLNe2 (SM : SectionModule Lu ⊥ V M) {K : Subgroup G} (hK : K ≤ V)
    (m : ↥(SM.sub K)) : toM2_LNe2 (psiLNe2 SM hK (pickLNe2 SM m)) = (m : M) :=
  (Classical.choose_spec (SM.mem_sub.mp m.2)).2

private lemma pickLNe2_unique (SM : SectionModule Lu ⊥ V M) {K : Subgroup G} (hK : K ≤ V)
    (x : ↥K) (m : ↥(SM.sub K)) (h : toM2_LNe2 (psiLNe2 SM hK x) = (m : M)) :
    x = pickLNe2 SM m :=
  psiLNe2_injective SM hK (Additive.ofMul.injective (h.trans (psi_pickLNe2 SM hK m).symm))

private noncomputable def kappaFunLNe2 (SM : SectionModule Lu ⊥ V M)
    (SW : SectionModule Λ W₀ W₁ W) {K : Subgroup G} (hKW : K ≤ W₁) (m : ↥(SM.sub K)) : W :=
  toW2_LNe2 (phiLNe2 SW hKW (pickLNe2 SM m))

private lemma kappaFunLNe2_add (SM : SectionModule Lu ⊥ V M) (SW : SectionModule Λ W₀ W₁ W)
    {K : Subgroup G} (hK : K ≤ V) (hKW : K ≤ W₁) (m₁ m₂ : ↥(SM.sub K)) :
    kappaFunLNe2 SM SW hKW (m₁ + m₂) = kappaFunLNe2 SM SW hKW m₁ + kappaFunLNe2 SM SW hKW m₂ := by
  have hp : pickLNe2 SM (m₁ + m₂) = pickLNe2 SM m₁ * pickLNe2 SM m₂ := by
    symm
    apply pickLNe2_unique SM hK
    rw [map_mul, toM2_mul_LNe2, psi_pickLNe2, psi_pickLNe2, Submodule.coe_add]
  unfold kappaFunLNe2
  rw [hp, map_mul, toW2_mul_LNe2]

private noncomputable def kappaLNe2 (SM : SectionModule Lu ⊥ V M) (SW : SectionModule Λ W₀ W₁ W)
    {K : Subgroup G} (hK : K ≤ V) (hKW : K ≤ W₁) : ↥(SM.sub K) →ₗ[ZMod 2] W :=
  (AddMonoidHom.mk' (kappaFunLNe2 SM SW hKW) (kappaFunLNe2_add SM SW hK hKW)).toZModLinearMap 2

theorem exists_kappa_LNe2 (SM : SectionModule Lu ⊥ V M) (SW : SectionModule Λ W₀ W₁ W)
    (hLuΛ : Lu ≤ Λ) {K U : Subgroup G} (hK : K ≤ V) (hKW : K ≤ W₁) (hUW : U ⊓ W₁ ≤ W₀)
    (hKinv : ∀ s : ↥Lu, ∀ c ∈ K, (s : G) * c * (s : G)⁻¹ ∈ K) :
    ∃ κ : ↥(SM.sub K) →ₗ[ZMod 2] W,
      LinearMap.range κ = SW.sub K ∧
      (∀ (s : ↥Lu) (v : ↥(SM.sub K)) (hv : SM.ρ s (v : M) ∈ SM.sub K),
        κ ⟨SM.ρ s (v : M), hv⟩ = (SW.ρ.comp (Subgroup.inclusion hLuΛ) s) (κ v)) ∧
      (∀ v : ↥(SM.sub K), (v : M) ∈ SM.sub U → κ v = 0) := by
  refine ⟨kappaLNe2 SM SW hK hKW, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rintro w ⟨v, rfl⟩
      exact SW.mem_sub_of_mem (x := ⟨(pickLNe2 SM v : G), hKW (pickLNe2 SM v).2⟩)
        (pickLNe2 SM v).2
    · intro w hw
      obtain ⟨x, hxK, hxw⟩ := SW.mem_sub.mp hw
      have hmem : toM2_LNe2 (SM.π ⟨(x : G), hK hxK⟩) ∈ SM.sub K :=
        SM.mem_sub_of_mem (x := ⟨(x : G), hK hxK⟩) hxK
      obtain ⟨m0, hm0⟩ : ∃ m0 : ↥(SM.sub K), (m0 : M) = toM2_LNe2 (SM.π ⟨(x : G), hK hxK⟩) :=
        ⟨⟨_, hmem⟩, rfl⟩
      have hp : (⟨(x : G), hxK⟩ : ↥K) = pickLNe2 SM m0 :=
        pickLNe2_unique SM hK ⟨(x : G), hxK⟩ m0 (by
          show toM2_LNe2 (SM.π ⟨(x : G), hK hxK⟩) = (m0 : M)
          rw [hm0])
      refine ⟨m0, ?_⟩
      show toW2_LNe2 (phiLNe2 SW hKW (pickLNe2 SM m0)) = w
      rw [← hp]
      exact hxw
  · intro s v hv
    have hsx : (s : G) * (pickLNe2 SM v : G) * (s : G)⁻¹ ∈ K :=
      hKinv s _ (pickLNe2 SM v).2
    have hA : SM.ρ s (v : M) =
        toM2_LNe2 (psiLNe2 SM hK ⟨(s : G) * (pickLNe2 SM v : G) * (s : G)⁻¹, hsx⟩) := by
      calc SM.ρ s (v : M)
          = SM.ρ s (toM2_LNe2 (psiLNe2 SM hK (pickLNe2 SM v))) := by
            rw [psi_pickLNe2]
        _ = toM2_LNe2 (psiLNe2 SM hK ⟨(s : G) * (pickLNe2 SM v : G) * (s : G)⁻¹, hsx⟩) :=
            SM.act s ⟨(pickLNe2 SM v : G), hK (pickLNe2 SM v).2⟩ (hK hsx)
    have hpick : pickLNe2 SM ⟨SM.ρ s (v : M), hv⟩ =
        ⟨(s : G) * (pickLNe2 SM v : G) * (s : G)⁻¹, hsx⟩ :=
      (pickLNe2_unique SM hK ⟨(s : G) * (pickLNe2 SM v : G) * (s : G)⁻¹, hsx⟩
        ⟨SM.ρ s (v : M), hv⟩ hA.symm).symm
    show toW2_LNe2 (phiLNe2 SW hKW (pickLNe2 SM ⟨SM.ρ s (v : M), hv⟩)) =
      SW.ρ (Subgroup.inclusion hLuΛ s) (toW2_LNe2 (phiLNe2 SW hKW (pickLNe2 SM v)))
    rw [hpick]
    exact (SW.act (Subgroup.inclusion hLuΛ s) ⟨(pickLNe2 SM v : G), hKW (pickLNe2 SM v).2⟩
      (hKW hsx)).symm
  · intro v hv
    obtain ⟨u, hu, hvu⟩ := SM.mem_sub.mp hv
    have hvu' : toM2_LNe2 (SM.π u) = (v : M) := hvu
    have hpsi : psiLNe2 SM hK (pickLNe2 SM v) = SM.π u :=
      Additive.ofMul.injective ((psi_pickLNe2 SM hK v).trans hvu'.symm)
    have hx : (pickLNe2 SM v : G) = (u : G) := by
      have h1 : (⟨(pickLNe2 SM v : G), hK (pickLNe2 SM v).2⟩ : ↥V) = u :=
        SM.π_injective_of_bot rfl hpsi
      have h2 := congrArg Subtype.val h1
      exact h2
    have hxU : (pickLNe2 SM v : G) ∈ U ⊓ W₁ := by
      refine Subgroup.mem_inf.mpr ⟨?_, hKW (pickLNe2 SM v).2⟩
      rw [hx]
      exact hu
    have hxW₀ : (pickLNe2 SM v : G) ∈ W₀ := hUW hxU
    have h1 : SW.π ⟨(pickLNe2 SM v : G), hKW (pickLNe2 SM v).2⟩ = 1 := (SW.ker _).mpr hxW₀
    show toW2_LNe2 (SW.π ⟨(pickLNe2 SM v : G), hKW (pickLNe2 SM v).2⟩) = 0
    exact (congrArg toW2_LNe2 h1).trans toW2_one_LNe2

private lemma normalizer_inf_LNe2 {Lu V W₁ : Subgroup G}
    (h1 : Lu ≤ Subgroup.normalizer (V : Set G)) (h2 : Lu ≤ Subgroup.normalizer (W₁ : Set G)) :
    Lu ≤ Subgroup.normalizer ((V ⊓ W₁ : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have e1 := Subgroup.mem_normalizer_iff.mp (h1 hs) h
  have e2 := Subgroup.mem_normalizer_iff.mp (h2 hs) h
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr e1 e2

end Kappa

theorem hb_group {G : Type} [Group G] [Finite G] {Λ Lu V U B₁ B W₀ W₁ : Subgroup G}
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (SW : SectionModule Λ W₀ W₁ W) (hLuΛ : Lu ≤ Λ)
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hVsq : ∀ v ∈ V, v * v = 1)
    (hLuV : Lu ≤ Subgroup.normalizer (V : Set G)) (hLuU : Lu ≤ Subgroup.normalizer (U : Set G))
    (hLuB₁ : Lu ≤ Subgroup.normalizer (B₁ : Set G)) (hLuB : Lu ≤ Subgroup.normalizer (B : Set G))
    (hUB₁ : U ≤ B₁) (hB₁B : B₁ ≤ B) (hBV : B ≤ V)
    (hirr : ∀ C : Subgroup G, U ≤ C → C ≤ B₁ → Lu ≤ Subgroup.normalizer (C : Set G) →
      C = U ∨ C = B₁)
    (hlt : U < B₁) (hcard : Nat.card ↥B₁ = 16 * Nat.card ↥U)
    (hnonab : ∃ x ∈ Lu, ∃ y ∈ Lu, ∃ b ∈ B₁, ⁅⁅x, y⁆, b⁆ ∉ U)
    (hBdim : Nat.card ↥B ≤ 2 * Nat.card ↥B₁)
    (hUW : U ⊓ W₁ ≤ W₀) (hVWB : V ⊓ W₁ ≤ B) :
    HBData (SW.img Lu) (SW.sub (V ⊓ W₁)) := by
  classical
  have h0 : Lu ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp
  have hab : ∀ x ∈ V, ∀ y ∈ V, x * y * x⁻¹ * y⁻¹ ∈ (⊥ : Subgroup G) := by
    intro x hx y hy
    rw [Subgroup.mem_bot]
    calc x * y * x⁻¹ * y⁻¹ = (x * y) * (y * x)⁻¹ := by group
      _ = 1 := by rw [hVc x hx y hy, mul_inv_cancel]
  have hsq : ∀ x ∈ V, x * x ∈ (⊥ : Subgroup G) := fun x hx => by
    rw [Subgroup.mem_bot]
    exact hVsq x hx
  obtain ⟨M, instAG, instMod, instFin, ⟨SM⟩⟩ :=
    exists_sectionModule (G := G) (Λ := Lu) (W₀ := ⊥) (W₁ := V) bot_le h0 hLuV hab hsq
  have hUV : U ≤ V := hUB₁.trans (hB₁B.trans hBV)
  have hB₁V : B₁ ≤ V := hB₁B.trans hBV
  have hLuW₁ : Lu ≤ Subgroup.normalizer (W₁ : Set G) := fun s hs => SW.norm₁ (hLuΛ hs)
  have hLuKV : Lu ≤ Subgroup.normalizer ((V ⊓ W₁ : Subgroup G) : Set G) :=
    normalizer_inf_LNe2 hLuV hLuW₁
  have hKinv : ∀ s : ↥Lu, ∀ c ∈ V ⊓ W₁, (s : G) * c * (s : G)⁻¹ ∈ V ⊓ W₁ :=
    fun s c hc => (Subgroup.mem_normalizer_iff.mp (hLuKV s.2) c).mp hc
  obtain ⟨κ, hκrange, hκeq, hκU⟩ :=
    exists_kappa_LNe2 SM SW hLuΛ inf_le_left inf_le_right hUW hKinv
  obtain ⟨hdimle, hfix, hirr'⟩ := hb_of_subquotient (S₀ := ↥Lu) (M := M) (W := W) SM.ρ
    (SW.ρ.comp (Subgroup.inclusion hLuΛ)) (SM.sub U) (SM.sub B₁) (SM.sub B) (SM.sub (V ⊓ W₁))
    (SW.sub (V ⊓ W₁))
    (fun s m hm => sub_inv_norm_LNe SM U hLuU s m hm)
    (fun s m hm => sub_inv_norm_LNe SM B₁ hLuB₁ s m hm)
    (fun s m hm => sub_inv_norm_LNe SM B hLuB s m hm)
    (fun s m hm => sub_inv_norm_LNe SM (V ⊓ W₁) hLuKV s m hm)
    (SM.sub_mono hUB₁) (SM.sub_mono hB₁B) (SM.sub_mono hVWB)
    (fun C hUC hCB hCinv => hirr_sm_LNe SM hLuV hUV hB₁V hirr C hUC hCB hCinv)
    (sub_ne_LNe SM hB₁V hlt) (finrank_sub_eq_add_four_LNe SM hB₁V hcard hUV)
    (hnonab_sm_LNe SM hLuV hLuB₁ hB₁V hnonab)
    (finrank_sub_le_add_one_LNe SM hBV hB₁V hBdim)
    κ hκrange hκeq hκU
  have memImg : ∀ s : ↥Lu, SW.ρ (Subgroup.inclusion hLuΛ s) ∈ SW.img Lu := fun s =>
    SW.mem_img.mpr ⟨Subgroup.inclusion hLuΛ s, s.2, rfl⟩
  refine ⟨?_, hdimle, ?_, ?_⟩
  · intro g hg w hw
    obtain ⟨y, hy, rfl⟩ := SW.mem_img.mp hg
    exact SW.sub_inv (V ⊓ W₁) y (fun c hc => (Subgroup.mem_normalizer_iff.mp (hLuKV hy) c).mp hc)
      w hw
  · intro P hP hfixP
    exact hfix P hP (fun s w hw => hfixP _ (memImg s) w hw)
  · intro P hP hPne hPinv hQ
    have hPinv' : ∀ s : ↥Lu, ∀ w ∈ P, (SW.ρ.comp (Subgroup.inclusion hLuΛ) s) w ∈ P :=
      fun s w hw => hPinv _ (memImg s) w hw
    have hQ' : ∀ Q : Submodule (ZMod 2) W, Q ≤ P →
        (∀ s : ↥Lu, ∀ w ∈ Q, (SW.ρ.comp (Subgroup.inclusion hLuΛ) s) w ∈ Q) →
          Q = ⊥ ∨ Q = P := by
      intro Q hQP hQinv
      apply hQ Q hQP
      intro g hg w hw
      obtain ⟨y, hy, rfl⟩ := SW.mem_img.mp hg
      exact hQinv ⟨y, hy⟩ w hw
    rcases hirr' P hP hPne hPinv' hQ' with h | ⟨h4, s, s', w, hw, hne⟩
    · exact Or.inl h
    · exact Or.inr ⟨h4, _, memImg s, _, memImg s', w, hw, hne⟩

end CFSG.Quasithin.H13.L829N
