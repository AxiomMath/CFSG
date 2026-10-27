module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81KFacts
import CFSG.ClassicalGroups.Symplectic.Simple

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

theorem ff81_t0 :
    ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ : G),
      FF81Basis b L B b₁ b₂ b₃ → Odd (Nat.card (CenS B)) →
      ∃ t₀ : G, orderOf t₀ = 2 ∧ t₀ ∈ CenS L ∧ t₀ * b * t₀⁻¹ = b⁻¹ := by
  intro G _ _ b L B b₁ b₂ b₃ hB hodd
  have h := hB.hyp
  have : IsSimpleGroup L :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp L 3 2 1 h.model
  obtain ⟨-, hBc, ⟨n, -, hn0, hn1, hn2, hn3⟩, -, -, -⟩ := hB.mono
  have hb3 : b ^ 3 = 1 := by rw [← h.ord]; exact pow_orderOf_eq_one b
  have hnC : ∀ c ∈ Cen b, n * c * n⁻¹ ∈ Cen b := fun c hc => by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have e : b = (n * b * n⁻¹)⁻¹ := by rw [hn0, inv_inv]
    calc n * c * n⁻¹ * b = n * c * n⁻¹ * (n * b * n⁻¹)⁻¹ := by rw [← e]
      _ = n * (c * b⁻¹) * n⁻¹ := by group
      _ = n * (b⁻¹ * c) * n⁻¹ := by
          rw [(Commute.inv_right (show Commute c b from hc)).eq]
      _ = (n * b * n⁻¹)⁻¹ * (n * c * n⁻¹) := by group
      _ = b * (n * c * n⁻¹) := by rw [← e]
  have hnC' : ∀ c ∈ Cen b, n⁻¹ * c * n ∈ Cen b := fun c hc => by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have e : b = n⁻¹ * b⁻¹ * n := by rw [← hn0]; group
    calc n⁻¹ * c * n * b = n⁻¹ * c * n * (n⁻¹ * b⁻¹ * n) := by rw [← e]
      _ = n⁻¹ * (c * b⁻¹) * n := by group
      _ = n⁻¹ * (b⁻¹ * c) * n := by
          rw [(Commute.inv_right (show Commute c b from hc)).eq]
      _ = (n⁻¹ * b⁻¹ * n) * (n⁻¹ * c * n) := by group
      _ = b * (n⁻¹ * c * n) := by rw [← e]
  set L' := L.map (MulAut.conj n).toMonoidHom with hL'
  have hmemL' : ∀ y, y ∈ L' ↔ ∃ x ∈ L, n * x * n⁻¹ = y := fun y => Iff.rfl
  have hLL' : ∀ l ∈ L, ∀ y ∈ L', l * y * l⁻¹ ∈ L' := by
    intro l hl y hy
    obtain ⟨x, hx, rfl⟩ := (hmemL' y).mp hy
    have hl0 : n⁻¹ * l * n ∈ Subgroup.normalizer (L : Set G) := h.hLN (hnC' l (h.hLC hl))
    have hx' := (Subgroup.mem_normalizer_iff.mp hl0 x).mp hx
    refine (hmemL' _).mpr ⟨_, hx', ?_⟩
    group
  have hB₁ : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ L ⊓ L' := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with hx | hx | hx <;> rw [hx]
    · exact ⟨hB.hb₁, (hmemL' _).mpr ⟨b₁, hB.hb₁, hn1⟩⟩
    · exact ⟨hB.hb₂, (hmemL' _).mpr ⟨b₂, hB.hb₂, hn2⟩⟩
    · exact ⟨hB.hb₃, (hmemL' _).mpr ⟨b₃, hB.hb₃, hn3⟩⟩
  have hN : ((L ⊓ L').subgroupOf L).Normal := ⟨fun x hx l => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨?_, ?_⟩
    · simpa using L.mul_mem (L.mul_mem l.2 hx.1) (L.inv_mem l.2)
    · simpa using hLL' l l.2 x hx.2⟩
  have hnL : n ∈ Subgroup.normalizer (L : Set G) := by
    rcases hN.eq_bot_or_eq_top with hbot | htop
    · exfalso
      have hc := hB.elem.2
      have hbot' : Subgroup.closure ({b₁, b₂, b₃} : Set G) = ⊥ := by
        refine eq_bot_iff.mpr fun x hx => ?_
        have hxL : x ∈ L := (hB₁ hx).1
        have : (⟨x, hxL⟩ : L) ∈ (L ⊓ L').subgroupOf L := Subgroup.mem_subgroupOf.mpr (hB₁ hx)
        rw [hbot, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
      rw [hbot', Subgroup.card_bot] at hc
      norm_num at hc
    · have hle : L ≤ L' := fun x hx => by
        have : (⟨x, hx⟩ : L) ∈ (L ⊓ L').subgroupOf L := htop ▸ Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp this).2
      have hcard : Nat.card L' ≤ Nat.card L :=
        (Subgroup.card_map_of_injective (MulAut.conj n).injective).le
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  obtain ⟨l, hlL, hl⟩ := kf_sp62Out G L h.model n hnL
  obtain ⟨m, hm⟩ : ∃ m, m = l⁻¹ * n := ⟨_, rfl⟩
  have hmL : m ∈ CenS L := Subgroup.mem_centralizer_iff.mpr fun x hx => by
    have := hl x hx
    calc x * m = l⁻¹ * (l * x * l⁻¹) * n := by rw [hm]; group
      _ = l⁻¹ * (n * x * n⁻¹) * n := by rw [this]
      _ = m * x := by rw [hm]; group
  have hlb : l * b = b * l := Subgroup.mem_centralizer_singleton_iff.mp (h.hLC hlL)
  have hmb : m * b * m⁻¹ = b⁻¹ := by
    have hlb' : l⁻¹ * b⁻¹ * l = b⁻¹ := by
      rw [(Commute.inv_inv (show Commute l b from hlb)).eq]; group
    calc m * b * m⁻¹ = l⁻¹ * (n * b * n⁻¹) * l := by rw [hm]; group
      _ = b⁻¹ := by rw [hn0, hlb']
  obtain ⟨c, hc⟩ : ∃ c, c = m * m := ⟨_, rfl⟩
  have hcb : c * b = b * c := by
    rw [hc]
    calc m * m * b = m * (m * b * m⁻¹) * m⁻¹ * m * m := by group
      _ = m * b⁻¹ * m⁻¹ * m * m := by rw [hmb]
      _ = (m * b * m⁻¹)⁻¹ * m * m := by group
      _ = b * (m * m) := by rw [hmb, inv_inv]; group
  have hcL : ∀ x ∈ L, x * c = c * x := fun x hx => by
    have := Subgroup.mem_centralizer_iff.mp hmL x hx
    calc x * c = x * m * m := by rw [hc, mul_assoc]
      _ = m * x * m := by rw [this]
      _ = m * (x * m) := mul_assoc _ _ _
      _ = m * (m * x) := by rw [this]
      _ = c * x := by rw [hc, mul_assoc]
  have hcB : c ∈ CenS B := by
    have hle : B ≤ Subgroup.centralizer {c} := by
      rw [hBc]
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hx with hx | hx | hx | hx <;> rw [hx]
      · exact hcb.symm
      · exact hcL _ hB.hb₁
      · exact hcL _ hB.hb₂
      · exact hcL _ hB.hb₃
    exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  set k := orderOf c with hk
  have hkodd : Odd k := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hcB)
  obtain ⟨j, hj⟩ := hkodd
  have hck : c ^ k = 1 := pow_orderOf_eq_one c
  have hcomm : Commute (c ^ j) b⁻¹ := ((Commute.pow_left hcb j)).inv_right
  have hmk : m ^ k = c ^ j * m := by
    rw [hj, pow_succ, pow_mul, hc, sq]
  refine ⟨m ^ k, orderOf_eq_prime ?_ ?_, Subgroup.pow_mem _ hmL k, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, sq, ← hc, hck]
  · intro h1
    have hbb : b = b⁻¹ := by
      have e : m ^ k * b * (m ^ k)⁻¹ = b⁻¹ := by
        rw [hmk]
        calc c ^ j * m * b * (c ^ j * m)⁻¹ = c ^ j * (m * b * m⁻¹) * (c ^ j)⁻¹ := by group
          _ = b⁻¹ := by rw [hmb, hcomm.eq]; group
      rw [h1] at e
      simpa using e
    have h2 : b ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [hbb]; exact mul_inv_cancel b
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h.ord] at this
    norm_num at this
  · rw [hmk]
    calc c ^ j * m * b * (c ^ j * m)⁻¹ = c ^ j * (m * b * m⁻¹) * (c ^ j)⁻¹ := by group
      _ = b⁻¹ := by rw [hmb, hcomm.eq]; group

end CFSG.RankThree.PartTwo.Sec21.FF81
