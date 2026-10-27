module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TPtAct
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TBlocks
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TCore5A
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TCtx

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open CFSG.Quasithin.H13.L828T
open scoped IsMulCommutative commutatorElement

section Rho

variable {G : Type} [Group G] [Finite G]

theorem s828_I_norm_P (T L I : Subgroup G) [IsMulCommutative ↥(fsuV T I)] (h : G) :
    ch82I (fsuV T I) h ≤ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem s828_LU_norm_U (T L I : Subgroup G) [IsMulCommutative ↥(fsuV T I)] (h : G) :
    ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) :=
  (perfectCore_le _).trans inf_le_right

theorem s828_LU_norm_P {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k) :
    ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) := by
  have hPI : pCoreOf 2 (ch82I (fsuV T I) h) ≤ ch82I (fsuV T I) h :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have h1 : ∀ l ∈ ch82LU L (ch82U (fsuV T I) h), ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h),
      l * p * l⁻¹ ∈ pCoreOf 2 (ch82I (fsuV T I) h) := by
    intro l hl p hp
    have h1 : ⁅p, l⁆ ∈ pCoreOf 2 (ch82I (fsuV T I) h) :=
      c.hILU (Subgroup.commutator_mem_commutator (hPI hp) hl)
    have e : l * p * l⁻¹ = (⁅p, l⁆)⁻¹ * p := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (pCoreOf 2 (ch82I (fsuV T I) h)).mul_mem
      ((pCoreOf 2 (ch82I (fsuV T I) h)).inv_mem h1) hp
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro p
  refine ⟨fun hp => h1 l hl p hp, fun hp => ?_⟩
  have := h1 l⁻¹ ((ch82LU L (ch82U (fsuV T I) h)).inv_mem hl) _ hp
  simpa [mul_assoc] using this

theorem s828_I_norm_PU {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k) :
    ch82I (fsuV T I) h ≤ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
      Subgroup.normalizer (ch82U (fsuV T I) h : Set G) := by
  intro i hi
  refine ⟨s828_I_norm_P T L I h hi, ?_⟩
  show i ∈ Subgroup.normalizer (ch82U (fsuV T I) h : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [c.hcen n hn i hi]
    exact hn
  · intro hn
    have := c.hcen _ hn i⁻¹ ((ch82I (fsuV T I) h).inv_mem hi)
    have e : i⁻¹ * (i * n * i⁻¹) * i⁻¹⁻¹ = n := by group
    rw [e] at this
    rw [this]
    exact hn

theorem s828_rho {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k) :
    ∃ ρ : ↥(Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
          Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) →*
        AddMonoid.End (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) ×
          QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)),
      (∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h), ∃ b₁ b₂ : ↥((ch82B (fsuV T I) h).subgroupOf (fsuV T I)),
        p * (((b₁ : ↥(fsuV T I)) : G) * h * ((b₂ : ↥(fsuV T I)) : G) * h⁻¹)⁻¹ ∈
          ch82U (fsuV T I) h) ∧
      (∀ (g : ↥(Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
          Subgroup.normalizer (ch82U (fsuV T I) h : Set G)))
          (b₁ b₂ : ↥((ch82B (fsuV T I) h).subgroupOf (fsuV T I))),
        ∃ β₁ β₂ : ↥((ch82B (fsuV T I) h).subgroupOf (fsuV T I)),
          PtCong (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) h g b₁ b₂ β₁ β₂) ∧
      (∀ (g : ↥(Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
          Subgroup.normalizer (ch82U (fsuV T I) h : Set G)))
          (b₁ b₂ β₁ β₂ : ↥((ch82B (fsuV T I) h).subgroupOf (fsuV T I))),
        PtCong (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) h g b₁ b₂ β₁ β₂ →
        ρ g (qb (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) b₁,
            qb (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) b₂) =
          (qb (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) β₁,
            qb (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) β₂)) ∧
      (∀ g : ↥(Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
          Subgroup.normalizer (ch82U (fsuV T I) h : Set G)),
        ρ g = 1 ↔ ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h),
          (g : G) * p * (g : G)⁻¹ * p⁻¹ ∈ ch82U (fsuV T I) h) ∧
      (∀ (y₀ : ↥(Subgroup.normalizer (fsuV T I : Set G)))
          (hy : (y₀ : G) ∈ ch82LU L (ch82U (fsuV T I) h))
          (γ : AddMonoid.End (QMod ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
            ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))),
        Induces γ (⇑(conjAct (fsuV T I) y₀)) →
        diagEnd γ = ρ ⟨(y₀ : G), s828_LU_norm_P c hy, s828_LU_norm_U T L I h hy⟩) ∧
      (∀ (i : ↥(Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
          Subgroup.normalizer (ch82U (fsuV T I) h : Set G)))
          (_ : (i : G) ∈ ch82I (fsuV T I) h)
          (γ : AddMonoid.End (QMod ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
            ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))),
        γ ∈ indSet ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
          ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
          ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
            Set (MulAut ↥(fsuV T I))) →
        ρ i * diagEnd γ = diagEnd γ * ρ i) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := fsuV T I with hVdef
  set Ih := ch82I V h with hIh
  set P := pCoreOf 2 Ih with hPdef
  set B := ch82B V h with hBdef
  set U := ch82U V h with hUdef
  set A := ch82A V h with hAdef
  set LU := ch82LU L U with hLUdef
  have hIP : Ih ≤ Subgroup.normalizer (P : Set G) := s828_I_norm_P T L I h
  have hPI : P ≤ Ih := CFSG.LieType.BorelTits.pCoreOf_le 2 Ih
  have hBV : B ≤ V := inf_le_left
  have hBP : B ≤ P := inf_le_right
  have hAP : A ≤ P := inf_le_right
  have hUA : U ≤ A := fun u hu =>
    ⟨(c.hUZ ▸ hu : u ∈ ch82ZI V h).2, hBP (c.hUB hu)⟩
  have hPU : ∀ u ∈ U, ∀ p ∈ P, p * u * p⁻¹ = u := fun u hu p hp => c.hcen u hu p (hPI hp)
  have hhU : ∀ u ∈ U, h * u * h⁻¹ = u := fun u hu => c.hcen u hu h c.hhI
  have hhB : ∀ b ∈ B, h * b * h⁻¹ ∈ A := by
    intro b hb
    refine ⟨B6.mem_conjSub.mpr ?_, (Subgroup.mem_normalizer_iff.mp (hIP c.hhI) b).mp (hBP hb)⟩
    have e : h⁻¹ * (h * b * h⁻¹) * h = b := by group
    rw [e]
    exact hBV hb
  have hhA : ∀ a ∈ A, h⁻¹ * a * h ∈ B := by
    intro a ha
    refine ⟨B6.mem_conjSub.mp ha.1, ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (hIP (Ih.inv_mem c.hhI)) a).mp (hAP ha)
    simpa using this
  have hAB : A ⊓ B ≤ U := fun x hx => by
    show x ∈ ch82U V h
    rw [c.hUZ]
    exact ⟨hBV hx.2, hx.1.1⟩
  obtain ⟨ρ, htot, hspec, hker⟩ := exists_ptAct (V := V) (B := B) (U := U) (P := P) (A := A)
    (h := h) c.hUB hBV hBP hAP hUA c.hPeq c.hP2 hPU (hIP c.hhI) hhU hhB hhA hAB
  have hsurj := exists_ptAct_surj (V := V) (B := B) (U := U) (P := P) (A := A) (h := h) hBV hBP
    hAP hUA c.hPeq c.hP2 hPU hhU hhB hhA hAB
  have hLUP := s828_LU_norm_P c
  have hLUU := s828_LU_norm_U T L I h
  have hIN2 := s828_I_norm_PU c
  have hdiag : ∀ (y₀ : ↥(Subgroup.normalizer (V : Set G))) (hy : (y₀ : G) ∈ LU)
      (γ : AddMonoid.End (QMod (B.subgroupOf V) (U.subgroupOf V))),
      Induces γ (⇑(conjAct V y₀)) →
      diagEnd γ = ρ ⟨(y₀ : G), hLUP hy, hLUU hy⟩ := by
    intro y₀ hyLU γ hγ
    apply AddMonoidHom.ext
    rintro ⟨e₁, e₂⟩
    obtain ⟨b₁, rfl⟩ := QMod.mk_surjective _ _ e₁
    obtain ⟨b₂, rfl⟩ := QMod.mk_surjective _ _ e₂
    obtain ⟨b₁', hb₁', hγ₁⟩ := hγ b₁
    obtain ⟨b₂', hb₂', hγ₂⟩ := hγ b₂
    have hb₁'G : ((b₁' : ↥V) : G) = (y₀ : G) * ((b₁ : ↥V) : G) * (y₀ : G)⁻¹ := by
      rw [hb₁']
      exact CFSG.QuasithinUnique.Setup.coe_conjAct_apply y₀ (b₁ : ↥V)
    have hb₂'G : ((b₂' : ↥V) : G) = (y₀ : G) * ((b₂ : ↥V) : G) * (y₀ : G)⁻¹ := by
      rw [hb₂']
      exact CFSG.QuasithinUnique.Setup.coe_conjAct_apply y₀ (b₂ : ↥V)
    have hb₂B : ((b₂ : ↥V) : G) ∈ B := Subgroup.mem_subgroupOf.mp b₂.2
    have hb₁'B : ((b₁' : ↥V) : G) ∈ B := Subgroup.mem_subgroupOf.mp b₁'.2
    have hcong : PtCong V B U h
        (⟨(y₀ : G), hLUP hyLU, hLUU hyLU⟩ :
          ↥(Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G))) b₁ b₂ b₁' b₂' := by
      unfold PtCong
      have hcomm0 : ⁅(y₀ : G), h⁆ ∈ pCoreOf 2 LU :=
        c.hcomm (Subgroup.commutator_mem_commutator hyLU c.hhI)
      have hx := x_comm_LU (P := P) (U := U) (x := (y₀ : G)) (l := h) (hIP c.hhI)
        (hLUP hyLU) (fun p hp => c.hO2P _ hcomm0 p hp) (b := ((b₂ : ↥V) : G)) (hBP hb₂B)
      rw [hb₁'G, hb₂'G]
      set β₁ : G := (y₀ : G) * ((b₁ : ↥V) : G) * (y₀ : G)⁻¹ with hβ₁
      have hβ₁B : β₁ ∈ Ih := hPI (hBP (by rw [← hb₁'G]; exact hb₁'B))
      have e : (y₀ : G) * (((b₁ : ↥V) : G) * h * ((b₂ : ↥V) : G) * h⁻¹) * (y₀ : G)⁻¹ *
          (β₁ * h * ((y₀ : G) * ((b₂ : ↥V) : G) * (y₀ : G)⁻¹) * h⁻¹)⁻¹ =
          β₁ * (((y₀ : G) * (h * ((b₂ : ↥V) : G) * h⁻¹) * (y₀ : G)⁻¹) *
            (h * ((y₀ : G) * ((b₂ : ↥V) : G) * (y₀ : G)⁻¹) * h⁻¹)⁻¹) * β₁⁻¹ := by
        rw [hβ₁]
        group
      rw [e, c.hcen _ hx β₁ hβ₁B]
      exact hx
    have hs := hspec ⟨(y₀ : G), hLUP hyLU, hLUU hyLU⟩ b₁ b₂ b₁' b₂' hcong
    refine Eq.trans ?_ hs.symm
    exact Prod.ext hγ₁ hγ₂
  refine ⟨ρ, hsurj, htot, hspec, hker, hdiag, ?_⟩
  intro i hiI γ hγ0
  obtain ⟨g, hg, hγ⟩ := hγ0
  obtain ⟨y₀, hy₀, hgy⟩ := Subgroup.mem_map.mp hg
  have hyLU : (y₀ : G) ∈ LU := Subgroup.mem_subgroupOf.mp hy₀
  have hy := hdiag y₀ hyLU γ (hgy ▸ hγ)
  rw [hy]
  set y : ↥(Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G)) :=
    ⟨(y₀ : G), hLUP hyLU, hLUU hyLU⟩ with hydef
  have hc1 : ρ (i * y * i⁻¹ * y⁻¹) = 1 := by
    rw [hker]
    intro p hp
    have hP' : ((i * y * i⁻¹ * y⁻¹ :
        ↥(Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G))) : G) ∈ P :=
      c.hILU (Subgroup.commutator_mem_commutator hiI hyLU)
    exact c.hP2 _ hP' p hp
  calc ρ i * ρ y = ρ (i * y) := (map_mul ρ i y).symm
    _ = ρ ((i * y * i⁻¹ * y⁻¹) * (y * i)) := by congr 1; group
    _ = ρ (i * y * i⁻¹ * y⁻¹) * ρ (y * i) := map_mul ρ _ _
    _ = ρ (y * i) := by rw [hc1, one_mul]
    _ = ρ y * ρ i := map_mul ρ y i

end Rho

end CFSG.Quasithin.H13
