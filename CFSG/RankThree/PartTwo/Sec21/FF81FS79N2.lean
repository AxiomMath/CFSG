module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Odd
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Frame

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

def R38Stmt (b : H) (A : Subgroup H) : Prop :=
  setMul (Opp 2 (Nor A)) (Nor (Subgroup.zpowers b) ⊓ Nor A) = Nor A

theorem mem_Nor_of_comm_all {A : Subgroup H} {g : H} (hg : ∀ y ∈ A, g * y = y * g) :
    g ∈ Nor A := by
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  have : g * y * g⁻¹ = y := by
    calc g * y * g⁻¹ = (y * g) * g⁻¹ := by rw [hg y hy]
      _ = y := by group
  rw [this]
  exact hy

namespace Std

variable (S : Std b t b₁ b₂ J)

include S

noncomputable def NJ (A₁ : Subgroup J6.S6) : Subgroup H := (Nor A₁).map S.ι

theorem ι_mem_Nor_map {A₁ : Subgroup J6.S6} {σ : J6.S6} (hσ : ∀ s ∈ A₁, σ * s * σ⁻¹ ∈ A₁) :
    S.ι σ ∈ Nor (A₁.map S.ι) := by
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨s, hs, rfl⟩ := hy
  rw [← map_mul, ← map_inv, ← map_mul]
  exact ⟨_, hσ s hs, rfl⟩

theorem t_mem_Nor_map (A₁ : Subgroup J6.S6) : t ∈ Nor (A₁.map S.ι) := by
  refine mem_Nor_of_comm_all fun y hy => ?_
  obtain ⟨s, -, rfl⟩ := hy
  exact (S.ι_comm_t s).symm

theorem frame_R_le_Nor {A₁ : Subgroup J6.S6}
    (hRN : ∀ r ∈ J6.R, ∀ s ∈ A₁, r * s * r⁻¹ ∈ A₁) :
    S.frame J6.R ≤ Nor (A₁.map S.ι) := by
  intro x hx
  obtain ⟨r, hr, rfl | rfl⟩ := (S.mem_frame_iff J6.R x).mp hx
  · exact S.ι_mem_Nor_map (hRN r hr)
  · exact (Nor (A₁.map S.ι)).mul_mem (S.t_mem_Nor_map A₁) (S.ι_mem_Nor_map (hRN r hr))

theorem frame_le_Nor_b (A₁ : Subgroup J6.S6) : S.frame A₁ ≤ Nor (Subgroup.zpowers b) := by
  intro x hx
  obtain ⟨s, hs, rfl | rfl⟩ := (S.mem_frame_iff A₁ x).mp hx
  · exact S.hyp.J_le_Nor (S.ι_mem s)
  · exact (Nor (Subgroup.zpowers b)).mul_mem S.hyp.t_mem_Nor (S.hyp.J_le_Nor (S.ι_mem s))

theorem M1_eq (A₁ : Subgroup J6.S6) :
    Nor (Subgroup.zpowers b) ⊓ Nor (A₁.map S.ι) =
      Opp 3 (Nor (Subgroup.zpowers b)) ⊔ (Subgroup.closure ({b, t} : Set H) ⊔ S.NJ A₁) := by
  classical
  have h := S.hyp
  apply le_antisymm
  · rintro n ⟨hnb, hnA⟩
    obtain ⟨hrM, hκ⟩ := h.rho_spec hnb
    set m : H := h.rho n with hm
    set κ : H := n * m⁻¹ with hκdef
    have hκM : κ ∈ Nor (Subgroup.zpowers b) ⊓ Nor (A₁.map S.ι) := by
      refine ⟨L14.Opp_le 3 _ hκ, mem_Nor_of_comm_all fun y hy => ?_⟩
      obtain ⟨s, -, rfl⟩ := hy
      exact h.K_comm_J hκ (S.ι_mem s)
    have hmM : m ∈ Nor (A₁.map S.ι) := by
      have : m = κ⁻¹ * n := by rw [hκdef]; group
      rw [this]
      exact (Nor (A₁.map S.ι)).mul_mem ((Nor (A₁.map S.ι)).inv_mem hκM.2) hnA
    obtain ⟨y, hy, j, hj, hyj⟩ := (CFSG.mem_sup_of_commute
      (A := Subgroup.closure ({b, t} : Set H)) (B := J)
      (fun a ha c hc => h.Y_comm_J ha hc)).mp hrM
    have hyN : y ∈ Nor (A₁.map S.ι) := mem_Nor_of_comm_all fun z hz => by
      obtain ⟨s, -, rfl⟩ := hz
      exact h.Y_comm_J hy (S.ι_mem s)
    have hjN : j ∈ Nor (A₁.map S.ι) := by
      have : j = y⁻¹ * m := by rw [← hyj]; group
      rw [this]
      exact (Nor (A₁.map S.ι)).mul_mem ((Nor (A₁.map S.ι)).inv_mem hyN) hmM
    have hjNJ : j ∈ S.NJ A₁ := by
      obtain ⟨σ, rfl⟩ := S.exists_ι hj
      refine ⟨σ, ?_, rfl⟩
      refine Subgroup.mem_normalizer_fintype fun s hs => ?_
      have h1 := (Subgroup.mem_normalizer_iff.mp hjN (S.ι s)).mp ⟨s, hs, rfl⟩
      rw [← map_mul, ← map_inv, ← map_mul] at h1
      obtain ⟨s', hs', hs'e⟩ := h1
      have := S.ι_injective hs'e
      rw [← this]
      exact hs'
    have hmY : m ∈ Subgroup.closure ({b, t} : Set H) ⊔ S.NJ A₁ := by
      rw [← hyj]
      exact Subgroup.mul_mem_sup hy hjNJ
    have hnκ : n = κ * m := by rw [hκdef]; group
    rw [hnκ]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hκ) (Subgroup.mem_sup_right hmY)
  · refine sup_le ?_ (sup_le ?_ ?_)
    · intro k hk
      exact ⟨L14.Opp_le 3 _ hk, mem_Nor_of_comm_all fun y hy => by
        obtain ⟨s, -, rfl⟩ := hy
        exact h.K_comm_J hk (S.ι_mem s)⟩
    · intro y hy
      exact ⟨h.Y_le_Nor hy, mem_Nor_of_comm_all fun z hz => by
        obtain ⟨s, -, rfl⟩ := hz
        exact h.Y_comm_J hy (S.ι_mem s)⟩
    · rintro _ ⟨σ, hσ, rfl⟩
      refine ⟨h.J_le_Nor (S.ι_mem σ), S.ι_mem_Nor_map fun s hs => ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp hσ s).mp hs


theorem NJ_le_J (A₁ : Subgroup J6.S6) : S.NJ A₁ ≤ J := by
  rintro _ ⟨σ, -, rfl⟩
  exact S.ι_mem σ

theorem card_M0₁ (A₁ : Subgroup J6.S6) (hN : Nat.card (Nor A₁) = 48) :
    Nat.card (Subgroup.closure ({b, t} : Set H) ⊔ S.NJ A₁ : Subgroup H) = 288 := by
  have h := S.hyp
  have hcomm : ∀ a ∈ Subgroup.closure ({b, t} : Set H), ∀ c ∈ S.NJ A₁, Commute a c := by
    intro a ha c hc
    obtain ⟨σ, -, rfl⟩ := hc
    exact h.Y_comm_J ha (S.ι_mem σ)
  have hdisj : Subgroup.closure ({b, t} : Set H) ⊓ S.NJ A₁ = ⊥ := by
    rw [eq_bot_iff, ← h.bt_inf_J]
    exact inf_le_inf_left _ (S.NJ_le_J A₁)
  rw [CFSG.card_sup_eq_mul_of_commute _ _ hcomm hdisj, h.card_bt]
  have : Nat.card (S.NJ A₁) = 48 := by
    unfold NJ
    rw [Subgroup.card_map_of_injective S.ι_injective, hN]
  rw [this]

theorem card_M1 (A₁ : Subgroup J6.S6) (hN : Nat.card (Nor A₁) = 48) :
    Nat.card (Nor (Subgroup.zpowers b) ⊓ Nor (A₁.map S.ι) : Subgroup H) =
      Nat.card (Opp 3 (Nor (Subgroup.zpowers b))) * 288 := by
  have h := S.hyp
  rw [S.M1_eq A₁, sup_comm]
  have hle : Subgroup.closure ({b, t} : Set H) ⊔ S.NJ A₁ ≤ Nor (Subgroup.zpowers b) :=
    sup_le h.Y_le_Nor ((S.NJ_le_J A₁).trans h.J_le_Nor)
  have hnorm : Subgroup.closure ({b, t} : Set H) ⊔ S.NJ A₁ ≤
      Subgroup.normalizer (Opp 3 (Nor (Subgroup.zpowers b)) : Set H) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    exact L14.Opp_conj_mem (hle hx) hz
  have hprod := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    hnorm
  have hinf : (Subgroup.closure ({b, t} : Set H) ⊔ S.NJ A₁) ⊓
      Opp 3 (Nor (Subgroup.zpowers b)) = ⊥ := by
    rw [eq_bot_iff, ← h.K_inf_M0, inf_comm]
    exact inf_le_inf_left _ (sup_le_sup_left (S.NJ_le_J A₁) _)
  rw [hinf, Subgroup.card_bot, mul_one, S.card_M0₁ A₁ hN] at hprod
  rw [hprod]
  ring

theorem isSylowOf_Nor_A₁H (A₁ : Subgroup J6.S6) (hN : Nat.card (Nor A₁) = 48)
    (hRN : ∀ r ∈ J6.R, ∀ s ∈ A₁, r * s * r⁻¹ ∈ A₁) (h38 : R38Stmt b (A₁.map S.ι)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S.frame J6.R) (Nor (A₁.map S.ι)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := S.hyp
  set L : Subgroup H := Nor (A₁.map S.ι) with hL
  set O₁ : Subgroup H := Opp 2 L with hO₁
  set M₁ : Subgroup H := Nor (Subgroup.zpowers b) ⊓ L with hM₁
  have hPL : S.frame J6.R ≤ L := S.frame_R_le_Nor hRN
  have hPcard : Nat.card (S.frame J6.R) = 32 := by rw [S.card_frame, J6.card_R]
  have hP2 : IsPGroup 2 (S.frame J6.R) := IsPGroup.of_card (n := 5) (by rw [hPcard]; norm_num)
  have hLeq : M₁ ⊔ O₁ = L := by
    apply le_antisymm
    · exact sup_le inf_le_right (L14.Opp_le 2 L)
    · intro n hn
      have hmem : n ∈ setMul O₁ M₁ := by
        rw [hO₁, hM₁, hL]
        have := h38
        unfold R38Stmt at this
        rw [this]
        exact hn
      obtain ⟨o, ho, m, hm, rfl⟩ := hmem
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ho) (Subgroup.mem_sup_left hm)
  have hnorm : M₁ ≤ Subgroup.normalizer (O₁ : Set H) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    exact L14.Opp_conj_mem hx.2 hz
  have hprod := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    hnorm
  rw [hLeq] at hprod
  have hM1card : Nat.card M₁ = Nat.card (Opp 3 (Nor (Subgroup.zpowers b))) * 288 :=
    S.card_M1 A₁ hN
  have hKodd := h.odd_K
  have hO₁odd : Odd (Nat.card O₁) := by
    have := L14.Opp_coprime 2 L
    exact Nat.coprime_two_left.mp this
  have hqodd : Odd (Nat.card (M₁ ⊓ O₁ : Subgroup H)) := by
    have hdvd : Nat.card (M₁ ⊓ O₁ : Subgroup H) ∣ Nat.card O₁ :=
      Subgroup.card_dvd_of_le inf_le_right
    exact Odd.of_dvd_nat hO₁odd hdvd
  have h1 := Subgroup.relIndex_mul_card (S.frame J6.R) L
  rw [inf_of_le_left hPL, hPcard] at h1
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨hPL, hP2, ?_⟩
  rintro ⟨r, hr⟩
  obtain ⟨k, hk⟩ := hKodd
  obtain ⟨o, ho⟩ := hO₁odd
  obtain ⟨q, hq⟩ := hqodd
  have e1 : (2 * r) * 32 * (2 * q + 1) = (2 * k + 1) * 288 * (2 * o + 1) := by
    calc (2 * r) * 32 * (2 * q + 1) = Nat.card L * Nat.card (M₁ ⊓ O₁ : Subgroup H) := by
          rw [← hr, h1, hq]
      _ = Nat.card M₁ * Nat.card O₁ := hprod
      _ = (2 * k + 1) * 288 * (2 * o + 1) := by rw [hM1card, hk, ho]
  have e2 : 32 * (2 * (r * (2 * q + 1))) = 32 * (9 * ((2 * k + 1) * (2 * o + 1))) := by
    linarith [e1]
  have e3 := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 32) e2
  have hodd : Odd (9 * ((2 * k + 1) * (2 * o + 1))) :=
    Odd.mul (by decide) (Odd.mul ⟨k, rfl⟩ ⟨o, rfl⟩)
  have := Nat.odd_iff.mp hodd
  omega

end Std

end CFSG.RankThree.PartTwo.Sec21.FF81
