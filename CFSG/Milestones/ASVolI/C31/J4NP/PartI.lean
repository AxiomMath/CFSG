module

public import CFSG.Milestones.ASVolI.C31.J4NP.Red

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4
open CFSG.Quasithin.J4Loc (omegaZ)

variable {R : Subgroup J}

theorem burnsideJ4NP_not_le_normalizer_conj (hR : burnsideJ4NP_Hyp R) {Y : Subgroup J}
    (hY : IsPGroup 2 ↥Y) (hne : Y ≠ ⊥) (hP0 : P0 ≤ Subgroup.normalizer (Y : Set J)) (g : J) :
    ¬ Subgroup.normalizer (R : Set J) ≤
      (Subgroup.normalizer (Y : Set J)).map (MulAut.conj g).toMonoidHom := by
  intro hle
  rw [← burnsideJ4NP_normalizer_map_conj] at hle
  have heq := hR.max _ (hY.map _) (burnsideJ4KW_map_conj_ne_bot hne g) hle
  apply hR.np g
  rw [← heq, burnsideJ4NP_normalizer_map_conj]
  exact Subgroup.map_mono hP0

theorem burnsideJ4NP_not_le_Hj_conj
    (hR : burnsideJ4NP_Hyp R) (g : J) :
    ¬ Subgroup.normalizer (R : Set J) ≤ Hj.map (MulAut.conj g).toMonoidHom := by
  have hF := j4Facts
  have hcard := card_Eg_uJ hF.mat
  rw [← normalizer_Eg_eq_Hj hF]
  refine burnsideJ4NP_not_le_normalizer_conj hR (IsPGroup.of_card hcard) ?_ ?_ g
  · intro h
    rw [h, Subgroup.card_bot] at hcard
    norm_num at hcard
  · rw [normalizer_Eg_eq_Hj hF]
    exact P0_le_Hj

theorem burnsideJ4NP_not_le_Cz0_conj
    (hR : burnsideJ4NP_Hyp R) (g : J) :
    ¬ Subgroup.normalizer (R : Set J) ≤
      (Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J)).map (MulAut.conj g).toMonoidHom := by
  intro hle
  refine burnsideJ4NP_not_le_normalizer_conj hR burnsideJ4NP_zpowers_z0.1
    burnsideJ4NP_zpowers_z0.2 ?_ g
    (hle.trans (Subgroup.map_mono (burnsideJ4NP_centralizer_le_normalizer_zpowers _)))
  intro x hx
  exact burnsideJ4NP_centralizer_le_normalizer_zpowers _
    (CFSG.Quasithin.E2P.J4Two.P0_le_centralizer hx)

theorem burnsideJ4NP_z0_mem_Z
    (hR : burnsideJ4NP_Hyp R) :
    CFSG.Quasithin.J4Loc.z0 ∈ omegaZ R := by
  obtain ⟨hz, hzc⟩ := burnsideJ4NP_z0_mem_cent hR
  refine ⟨hz, fun y hy => ?_, burnsideJ4NP_z0_sq⟩
  exact (Subgroup.mem_centralizer_iff.mp hzc y hy).symm

theorem burnsideJ4NP_Z_isPGroup (hR : burnsideJ4NP_Hyp R) : IsPGroup 2 ↥(omegaZ R) :=
  hR.p2.to_le (CFSG.Quasithin.J4Loc.omegaZ_le R)

theorem burnsideJ4NP_Z_ne_bot
    (hR : burnsideJ4NP_Hyp R) :
    omegaZ R ≠ ⊥ := by
  intro h
  have hz := burnsideJ4NP_z0_mem_Z hR
  rw [h, Subgroup.mem_bot] at hz
  exact CFSG.Quasithin.J4Loc.z0_ne_one j4Facts.mat hz

theorem burnsideJ4NP_normalizer_le_normalizer_Z (R : Subgroup J) :
    Subgroup.normalizer (R : Set J) ≤ Subgroup.normalizer (omegaZ R : Set J) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => CFSG.Quasithin.J4Loc.omegaZ_conj hg hx
  · intro hx
    have h1 := CFSG.Quasithin.J4Loc.omegaZ_conj (Subgroup.inv_mem _ hg) hx
    simpa [mul_assoc] using h1

theorem burnsideJ4NP_normalizer_Z
    (hR : burnsideJ4NP_Hyp R) :
    Subgroup.normalizer (omegaZ R : Set J) = Subgroup.normalizer (R : Set J) :=
  hR.max _ (burnsideJ4NP_Z_isPGroup hR) (burnsideJ4NP_Z_ne_bot hR)
    (burnsideJ4NP_normalizer_le_normalizer_Z R)

theorem burnsideJ4NP_Z_closed (hR : burnsideJ4NP_Hyp R) :
    omegaZ (P0 ⊓ Subgroup.centralizer (omegaZ R : Set J)) = omegaZ R := by
  have hRC : R ≤ P0 ⊓ Subgroup.centralizer (omegaZ R : Set J) := by
    refine le_inf hR.le fun r hr => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hx.2.1 r hr
  ext x
  constructor
  · rintro ⟨hxC, hxc, hxs⟩
    have hxR : x ∈ R := by
      apply hR.cent
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (hxc r (hRC hr)).symm
    exact ⟨hxR, fun y hy => hxc y (hRC hy), hxs⟩
  · rintro ⟨hxR, hxc, hxs⟩
    refine ⟨hRC hxR, fun y hy => ?_, hxs⟩
    have hyC : y ∈ Subgroup.centralizer (omegaZ R : Set J) := (Subgroup.mem_inf.mp hy).2
    have hxZ : x ∈ omegaZ R := ⟨hxR, hxc, hxs⟩
    exact Subgroup.mem_centralizer_iff.mp hyC x hxZ

theorem burnsideJ4NP_normalizer_le_normalizer_centralizer {G : Type*} [Group G] (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ c ∈ Subgroup.centralizer (X : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa using this
    have h1 := hc _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * x := by group
  intro c
  constructor
  · exact key g hg c
  · intro hc
    have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hc
    simpa [mul_assoc] using this

theorem burnsideJ4NP_conj_mem_pCoreOf {G : Type*} [Group G] {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 K) :
    g * x * g⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  let φ : ↥K ≃* ↥K :=
    ((MulAut.conj g).subgroupMap K).trans
      (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg))
  obtain ⟨y, hy, rfl⟩ := hx
  have hfix := (inferInstance : (CFSG.pCore 2 ↥K).Characteristic).fixed φ
  have hy' : φ y ∈ CFSG.pCore 2 ↥K := by
    have : y ∈ (CFSG.pCore 2 ↥K).comap φ.toMonoidHom := by rw [hfix]; exact hy
    exact Subgroup.mem_comap.mp this
  exact ⟨φ y, hy', rfl⟩

theorem burnsideJ4NP_normalizer_le_normalizer_pCoreOf {G : Type*} [Group G] (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => burnsideJ4NP_conj_mem_pCoreOf hg hx, fun hx => ?_⟩
  have := burnsideJ4NP_conj_mem_pCoreOf (Subgroup.inv_mem _ hg) hx
  simpa [mul_assoc] using this

@[expose] noncomputable def burnsideJ4NP_W (R : Subgroup J) : Subgroup J :=
  Subgroup.closure {x | x ∈ omegaZ R ∧ ∃ g : J, x = g * CFSG.Quasithin.J4Loc.z0 * g⁻¹}

theorem burnsideJ4NP_W_le_Z (R : Subgroup J) : burnsideJ4NP_W R ≤ omegaZ R := by
  rw [burnsideJ4NP_W, Subgroup.closure_le]
  rintro x ⟨hx, -⟩
  exact hx

theorem burnsideJ4NP_z0_mem_W
    (hR : burnsideJ4NP_Hyp R) :
    CFSG.Quasithin.J4Loc.z0 ∈ burnsideJ4NP_W R :=
  Subgroup.subset_closure ⟨burnsideJ4NP_z0_mem_Z hR, 1, by group⟩

theorem burnsideJ4NP_normalizer_le_normalizer_W (R : Subgroup J) :
    Subgroup.normalizer (R : Set J) ≤ Subgroup.normalizer (burnsideJ4NP_W R : Set J) := by
  have key : ∀ g ∈ Subgroup.normalizer (R : Set J), ∀ x ∈ burnsideJ4NP_W R,
      g * x * g⁻¹ ∈ burnsideJ4NP_W R := by
    intro g hg x hx
    rw [burnsideJ4NP_W] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hyZ, c, rfl⟩ := hy
      refine Subgroup.subset_closure ⟨CFSG.Quasithin.J4Loc.omegaZ_conj hg hyZ, g * c, ?_⟩
      group
    | one => simp
    | mul y w _ _ hy hw =>
      have e : g * (y * w) * g⁻¹ = (g * y * g⁻¹) * (g * w * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hy hw
    | inv y _ hy =>
      have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hy
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

theorem burnsideJ4NP_W_isPGroup_ne_bot
    (hR : burnsideJ4NP_Hyp R) : IsPGroup 2 ↥(burnsideJ4NP_W R) ∧ burnsideJ4NP_W R ≠ ⊥ := by
  refine ⟨(burnsideJ4NP_Z_isPGroup hR).to_le (burnsideJ4NP_W_le_Z R), fun h => ?_⟩
  have hz := burnsideJ4NP_z0_mem_W hR
  rw [h, Subgroup.mem_bot] at hz
  exact CFSG.Quasithin.J4Loc.z0_ne_one j4Facts.mat hz

theorem burnsideJ4NP_normalizer_W
    (hR : burnsideJ4NP_Hyp R) :
    Subgroup.normalizer (burnsideJ4NP_W R : Set J) = Subgroup.normalizer (R : Set J) :=
  hR.max _ (burnsideJ4NP_W_isPGroup_ne_bot hR).1 (burnsideJ4NP_W_isPGroup_ne_bot hR).2
    (burnsideJ4NP_normalizer_le_normalizer_W R)

theorem burnsideJ4NP_R_le_centralizer_W (R : Subgroup J) :
    R ≤ Subgroup.centralizer (burnsideJ4NP_W R : Set J) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (burnsideJ4NP_W_le_Z R hw).2.1 r hr

theorem burnsideJ4NP_R_eq_pCore_W
    (hR : burnsideJ4NP_Hyp R) :
    R = CFSG.Open.pCoreOf 2 (Subgroup.centralizer (burnsideJ4NP_W R : Set J)) := by
  have hCN : Subgroup.centralizer (burnsideJ4NP_W R : Set J) ≤ Subgroup.normalizer (R : Set J) := by
    rw [← burnsideJ4NP_normalizer_W hR]
    exact Subgroup.centralizer_le_normalizer _
  apply le_antisymm
  · exact burnsideJ4KW_le_pCoreOf hR.p2 (burnsideJ4NP_R_le_centralizer_W R) hCN
  · apply hR.core _ (burnsideJ4KW_isPGroup_pCoreOf _)
    refine le_trans ?_ (burnsideJ4NP_normalizer_le_normalizer_pCoreOf _)
    rw [← burnsideJ4NP_normalizer_W hR]
    exact burnsideJ4NP_normalizer_le_normalizer_centralizer _

theorem burnsideJ4NP_cl_le {G : Type*} [Group G] [Finite G] {H B PA PB : Subgroup G}
    (hB : omegaZ PB = B) (hPB : PB ≤ H ⊓ Subgroup.centralizer (B : Set G))
    (hPBmax : ∀ Q : Subgroup G, Q ≤ H ⊓ Subgroup.centralizer (B : Set G) → IsPGroup 2 ↥Q →
      PB ≤ Q → Q = PB)
    (hPA : PA ≤ H) (hPA2 : IsPGroup 2 ↥PA) (hle : PB ≤ PA) :
    omegaZ PA ≤ B := by
  intro x hx
  obtain ⟨hxPA, hxc, hxs⟩ := hx
  have hBPB : B ≤ PB := hB ▸ CFSG.Quasithin.J4Loc.omegaZ_le PB
  set Q := Subgroup.closure (insert x (PB : Set G)) with hQ
  have hQPA : Q ≤ PA := by
    rw [hQ, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact hxPA
    · exact hle hy
  have hQ2 : IsPGroup 2 ↥Q := hPA2.to_le hQPA
  have hQC : Q ≤ H ⊓ Subgroup.centralizer (B : Set G) := by
    rw [hQ, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact ⟨hPA hxPA, Subgroup.mem_centralizer_iff.mpr fun b hb => (hxc b (hle (hBPB hb))).symm⟩
    · exact hPB hy
  have hPBQ : PB ≤ Q := fun y hy => Subgroup.subset_closure (Set.mem_insert_of_mem _ hy)
  have hxQ : x ∈ Q := Subgroup.subset_closure (Set.mem_insert _ _)
  have heq := hPBmax Q hQC hQ2 hPBQ
  rw [heq] at hxQ
  rw [← hB]
  exact ⟨hxQ, fun y hy => hxc y (hle hy), hxs⟩

theorem burnsideJ4NP_le_omegaZ_of_max {G : Type*} [Group G] [Finite G] {H A PA : Subgroup G}
    (hAH : A ≤ H) (hA2 : IsPGroup 2 ↥A) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAs : ∀ a ∈ A, a * a = 1) (hPA : PA ≤ H ⊓ Subgroup.centralizer (A : Set G))
    (hPA2 : IsPGroup 2 ↥PA)
    (hPAmax : ∀ Q : Subgroup G, Q ≤ H ⊓ Subgroup.centralizer (A : Set G) → IsPGroup 2 ↥Q →
      PA ≤ Q → Q = PA) :
    A ≤ omegaZ PA := by
  have hAPA : A ≤ PA := by
    have hcomm : ∀ a ∈ A, ∀ p ∈ PA, a * p = p * a := by
      intro a ha p hp
      exact Subgroup.mem_centralizer_iff.mp (hPA hp).2 a ha
    have hsup2 : IsPGroup 2 ↥(A ⊔ PA) := by
      have hn : PA ≤ Subgroup.normalizer (A : Set G) := by
        intro p hp
        rw [Subgroup.mem_normalizer_iff]
        intro a
        constructor
        · intro ha
          rw [← hcomm a ha p hp, mul_inv_cancel_right]
          exact ha
        · intro ha
          have h1 := hcomm _ ha p hp
          have e : a = p * a * p⁻¹ :=
            calc a = p⁻¹ * ((p * a * p⁻¹) * p) := by group
              _ = p⁻¹ * (p * (p * a * p⁻¹)) := by rw [h1]
              _ = p * a * p⁻¹ := by group
          rw [e]
          exact ha
      exact hA2.to_sup_of_normal_left' hPA2 hn
    have hsupC : A ⊔ PA ≤ H ⊓ Subgroup.centralizer (A : Set G) := by
      refine sup_le (le_inf hAH fun a ha => ?_) hPA
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hAc b hb a ha
    have heq := hPAmax _ hsupC hsup2 le_sup_right
    rw [← heq]
    exact le_sup_left
  intro a ha
  refine ⟨hAPA ha, fun y hy => ?_, hAs a ha⟩
  exact Subgroup.mem_centralizer_iff.mp (hPA hy).2 a ha

@[expose] def burnsideJ4NP_OpenW : Prop :=
  ∀ R : Subgroup J, burnsideJ4NP_Hyp R →
    ∃ c : J, burnsideJ4NP_F.map (MulAut.conj c).toMonoidHom ≤ burnsideJ4NP_W R

theorem burnsideJ4NP_openLeF_of_openW
    (h : burnsideJ4NP_OpenW) : burnsideJ4NP_OpenLeF := by
  intro R hR
  obtain ⟨c, hc⟩ := h R hR
  refine ⟨c, fun r hr => ?_⟩
  rw [burnsideJ4NP_mem_map_conj, burnsideJ4NP_F_eq, ← burnsideJ4NP_centralizer_F4]
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hf' : c * f * c⁻¹ ∈ burnsideJ4NP_W R := by
    apply hc
    rw [burnsideJ4NP_mem_map_conj, burnsideJ4NP_F_eq]
    simpa [mul_assoc] using hf
  have h1 := Subgroup.mem_centralizer_iff.mp (burnsideJ4NP_R_le_centralizer_W R hr) _ hf'
  calc f * (c⁻¹ * r * c) = c⁻¹ * ((c * f * c⁻¹) * r) * c := by group
    _ = c⁻¹ * (r * (c * f * c⁻¹)) * c := by rw [h1]
    _ = c⁻¹ * r * c * f := by group

theorem burnsideJ4NP_maxNonParabolicP0_of_openW
    (h : burnsideJ4NP_OpenW) : burnsideJ4KW_MaxNonParabolicP0 :=
  burnsideJ4NP_maxNonParabolicP0_of_openLeF (burnsideJ4NP_openLeF_of_openW h)

end CFSG.ASVolI
