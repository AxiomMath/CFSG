module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieV
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOutAbs
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieCtr
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieLev

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin

section Generic

variable {G : Type*} [Group G]

theorem vee_conj_mem {V R H : Subgroup G} (hV : H ≤ Subgroup.normalizer (V : Set G))
    (hR : H ≤ Subgroup.normalizer (R : Set G)) {g v : G} (hg : g ∈ H)
    (hv : v ∈ V ⊓ Subgroup.centralizer (R : Set G)) :
    g⁻¹ * v * g ∈ V ⊓ Subgroup.centralizer (R : Set G) := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp (hV (H.inv_mem hg)) v).mp hv.1
    simpa using this
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : g * w * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hR hg) w).mp hw
    have e := Subgroup.mem_centralizer_iff.mp hv.2 _ hw'
    calc w * (g⁻¹ * v * g) = g⁻¹ * ((g * w * g⁻¹) * v) * g := by group
      _ = g⁻¹ * (v * (g * w * g⁻¹)) * g := by rw [e]
      _ = g⁻¹ * v * g * w := by group

end Generic

section Main

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

@[expose] def vee_B (C : Subgroup (MulAut (Xg h))) : Subgroup (GL (Fin 4) K) :=
  (C.comap (MulAut.conj : Xg h →* MulAut (Xg h))).map (gramSU h (miyamotoJ4 K)).subtype

theorem vee_mem_B {C : Subgroup (MulAut (Xg h))} {g : GL (Fin 4) K} :
    g ∈ vee_B h C ↔ ∃ a : Xg h, cj h a ∈ C ∧ (a : GL (Fin 4) K) = g := by
  unfold vee_B
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem vee_normalizer (F : Subgroup (K ≃+* K)) :
    Ssd h (Ln h) (fStab_Ln h) F ≤
      Subgroup.normalizer (Ssd h (A1X h) (fStab_A1X h) ⊥ : Set (MulAut (Xg h))) := by
  have key : ∀ β ∈ Ssd h (Ln h) (fStab_Ln h) F, ∀ v ∈ Ssd h (A1X h) (fStab_A1X h) ⊥,
      β * v * β⁻¹ ∈ Ssd h (A1X h) (fStab_A1X h) ⊥ := by
    rintro _ ⟨s, hs, φ, hφ, rfl⟩ v hv
    obtain ⟨a, ha, rfl⟩ := vee_cj_of_mem_Ssd_bot h hv
    rw [aut_mul_cj_mul_inv h]
    refine cj_mem_Ssd h ?_
    show s * fa h φ a * s⁻¹ ∈ A1X h
    exact (Subgroup.mem_normalizer_iff.mp hs _).mp ((fStab_A1X h φ a).mpr ha)
  intro α hα
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key α hα x hx, fun hx => ?_⟩
  have := key α⁻¹ ((Ssd h (Ln h) (fStab_Ln h) F).inv_mem hα) _ hx
  simpa [mul_assoc] using this

theorem vee_isPGroup : IsPGroup 2 ↥(Ssd h (A1X h) (fStab_A1X h) ⊥) := fun g =>
  ⟨1, Subtype.ext (by simpa using (Ssd_A1X_elemAb h).2 g g.2)⟩

theorem pCoreOf_Ssd_Ln (hf : 2 ≤ f) (F : Subgroup (K ≃+* K)) :
    pCoreOf 2 (Ssd h (Ln h) (fStab_Ln h) F) = Ssd h (A1X h) (fStab_A1X h) ⊥ := by
  have _hf := hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Ssd h (Ln h) (fStab_Ln h) F with hH
  set V := Ssd h (A1X h) (fStab_A1X h) ⊥ with hV
  have hVH : V ≤ H := Ssd_mono h (A1X_le_Ln h) bot_le
  have hVn : H ≤ Subgroup.normalizer (V : Set (MulAut (Xg h))) := vee_normalizer h F
  refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVH hVn
    (vee_isPGroup h))
  set R := pCoreOf 2 H with hR
  have hRH : R ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hRn : H ≤ Subgroup.normalizer (R : Set (MulAut (Xg h))) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hRp : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hVne : V ≠ ⊥ := by
    intro e
    have hm : cj h (z1X h) ∈ V := cj_mem_Ssd h (z1X_mem_A1X h)
    rw [e, Subgroup.mem_bot] at hm
    have := orderOf_cj_z1X h
    rw [hm, orderOf_one] at this
    exact absurd this (by norm_num)
  obtain ⟨z, hzV, hz1, hzR⟩ := exists_fixed_ne_one hRp (vee_isPGroup h) hVne
    (fun n hn x hx => (Subgroup.mem_normalizer_iff.mp (hVn (hRH hn)) x).mp hx)
  have hB1 : vee_B h (V ⊓ Subgroup.centralizer (R : Set (MulAut (Xg h)))) ≤ miyamotoA1 h := by
    intro x hx
    obtain ⟨a, haC, rfl⟩ := (vee_mem_B h).1 hx
    obtain ⟨s, hs, hcj⟩ := vee_cj_of_mem_Ssd_bot h haC.1
    have : a = s := (cj_inj h).1 hcj
    subst this
    exact hs
  have hBinv : ∀ n ∈ miyamotoN1 h, ∀ x ∈ vee_B h (V ⊓ Subgroup.centralizer
      (R : Set (MulAut (Xg h)))), n⁻¹ * x * n ∈ vee_B h (V ⊓ Subgroup.centralizer
        (R : Set (MulAut (Xg h)))) := by
    intro n hn x hx
    obtain ⟨a, haC, rfl⟩ := (vee_mem_B h).1 hx
    have hnX : (⟨n, miyamotoN1_le_gramSU h hn⟩ : Xg h) ∈ Ln h := by
      rw [Ln_eq h]
      exact Subgroup.mem_sup_right (Subgroup.mem_sup_right hn)
    refine (vee_mem_B h).2 ⟨(⟨n, miyamotoN1_le_gramSU h hn⟩ : Xg h)⁻¹ * a *
      ⟨n, miyamotoN1_le_gramSU h hn⟩, ?_, rfl⟩
    rw [cj_mul, cj_mul, cj_inv]
    exact vee_conj_mem hVn hRn (cj_mem_Ssd h hnX) haC
  have hBne : vee_B h (V ⊓ Subgroup.centralizer (R : Set (MulAut (Xg h)))) ≠ ⊥ := by
    obtain ⟨a, ha, hza⟩ := vee_cj_of_mem_Ssd_bot h hzV
    intro e
    have hzC : z ∈ V ⊓ Subgroup.centralizer (R : Set (MulAut (Xg h))) :=
      Subgroup.mem_inf.2 ⟨hzV, Subgroup.mem_centralizer_iff.2 fun n hn => by
        have := hzR n hn
        calc n * z = n * z * n⁻¹ * n := by group
          _ = z * n := by rw [this]⟩
    have hmem : (a : GL (Fin 4) K) ∈ vee_B h (V ⊓ Subgroup.centralizer
        (R : Set (MulAut (Xg h)))) := (vee_mem_B h).2 ⟨a, hza ▸ hzC, rfl⟩
    rw [e, Subgroup.mem_bot] at hmem
    have h1 : a = 1 := Subtype.ext hmem
    rw [h1, cj_one] at hza
    exact hz1 hza
  have hBtop := (miyamotoN1_irreducible_A1 h hB1 hBinv).resolve_left hBne
  intro w hw
  have hfix : ∀ g : Xg h, (g : GL (Fin 4) K) ∈ miyamotoA1 h → w g = g := by
    intro g hg
    have hgB : (g : GL (Fin 4) K) ∈ vee_B h (V ⊓ Subgroup.centralizer
        (R : Set (MulAut (Xg h)))) := by
      rw [hBtop]
      exact hg
    obtain ⟨a, haC, hag⟩ := (vee_mem_B h).1 hgB
    have ha : a = g := Subtype.ext hag
    subst ha
    have e := Subgroup.mem_centralizer_iff.mp haC.2 w hw
    have : cj h (w a) = cj h a := by
      rw [← aut_mul_cj_mul_inv h w a, e]
      group
    exact (cj_inj h).1 this
  obtain ⟨a₀, ha₀, hwe⟩ := (fixes_miyamotoA1_iff h w).1 hfix
  rw [hwe]
  exact cj_mem_Ssd h ha₀

end Main

end CFSG.Quasithin.H13.F431.Un.OL
