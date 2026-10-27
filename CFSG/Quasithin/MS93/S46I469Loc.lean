module

public import CFSG.Quasithin.MS93.S46I469Grp
public import CFSG.Quasithin.MS93.S46I469Lin
public import CFSG.Quasithin.MS93.S46I466b

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46.I464 CFSG.Quasithin.MS93.S46.I466b
open scoped Matrix commutatorElement

section Def

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def IsOddL1 (α β : Vtx X) (g : X.Universal) : Prop :=
  g ∈ stab X α ∧ g ∈ Subgroup.normalizer (Qv X β : Set X.Universal) ∧
    (∀ z ∈ ZM X α, ⁅z, g⁆ ∈ ZH X β) ∧ Odd (orderOf g)

end Def

section Loc

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
  (hsq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F ^ 2)
  (h466 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    (Qv (puAmalgam h.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2)
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

omit [Fintype F] in
include h464 in
theorem commutator_vv_qv_le_zh {β : Vtx (puAmalgam h.le)} (hβ : ¬ IsMVtx (puAmalgam h.le) β) :
    ⁅Vv (puAmalgam h.le) β, Qv _ β⁆ ≤ ZH _ β := by
  rw [vv_eq_iSup_of_not_isMVtx hβ]
  refine commutator_iSup₂_le_of (fun δ hδ => ?_) (fun δ hδ => ?_)
  · have hδM : IsMVtx 𝔛 δ := by have := isMVtx_iff_of_adj _ hδ; tauto
    have := h464 δ β hδM hδ.symm
    rwa [Usup, zv_of_isMVtx _ hδM] at this
  · have hδM : IsMVtx 𝔛 δ := by have := isMVtx_iff_of_adj _ hδ; tauto
    have hZT : ZM 𝔛 δ ≤ Qv 𝔛 β :=
      (zm_le_qv_self _ hδM h.critDist_pos).trans (qv_le_qv _ h.hyp20 hδM hδ.symm)
    refine hZT.trans ?_
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have key : ∀ s ∈ Qv 𝔛 β, ∀ y ∈ ZH 𝔛 β, s * y * s⁻¹ ∈ ZH 𝔛 β := fun s hs y hy => by
      rw [Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β hy) s hs, mul_inv_cancel_right]
      exact hy
    refine ⟨key t ht z, fun hz => ?_⟩
    have := key t⁻¹ (Subgroup.inv_mem _ ht) _ hz
    simpa [mul_assoc] using this

omit [Fintype F] in
theorem vv_mul_self_eq_one (hb : 2 < critDist (puAmalgam h.le)) {β : Vtx (puAmalgam h.le)}
    (hβ : ¬ IsMVtx (puAmalgam h.le) β) {x : 𝔘} (hx : x ∈ Vv (puAmalgam h.le) β) : x * x = 1 := by
  have h1 := sq_mem_commutator_vv h (by omega : 0 < critDist 𝔛) hx
  have h2 : ⁅Vv 𝔛 β, Vv 𝔛 β⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (vv_le_centralizer_of_not_isMVtx h.hyp20 hb hβ)
  rw [h2, Subgroup.mem_bot, sq] at h1
  exact h1

omit [Fintype F] in
theorem vv_comm (hb : 2 < critDist (puAmalgam h.le)) {β : Vtx (puAmalgam h.le)}
    (hβ : ¬ IsMVtx (puAmalgam h.le) β) {x y : 𝔘} (hx : x ∈ Vv (puAmalgam h.le) β)
    (hy : y ∈ Vv (puAmalgam h.le) β) : x * y = y * x :=
  Subgroup.mem_centralizer_iff.mp (vv_le_centralizer_of_not_isMVtx h.hyp20 hb hβ hy) x hx

include hφ h464 hsq in
theorem mem_usup_iff {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1)
    (u : ↥(Uloc h.le L α)) :
    (u : 𝔘) ∈ Usup (puAmalgam h.le) α β ↔
      natVec hψ u ∈ fixN (natImage ψ (Qv (puAmalgam h.le) β)) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hT : Qv 𝔛 β ≤ stab 𝔛 α := qv_le_stab_of_adj _ hαβ.symm
  obtain ⟨-, hcf⟩ := fixN_natImage_qv h hφ h464 hsq hα hαβ hψ
  rw [S4A.usup_eq_commutator_uloc h hfull hα hαβ, mem_commutator_iff_natVec hψ hT u, hcf]

include hφ h464 hsq in
theorem mem_usup_of_commute {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) {u : 𝔘} (hu : u ∈ Uloc h.le L α)
    (hc : ∀ t ∈ Qv (puAmalgam h.le) β, t * u = u * t) : u ∈ Usup (puAmalgam h.le) α β := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  have hT : Qv 𝔛 β ≤ stab 𝔛 α := qv_le_stab_of_adj _ hαβ.symm
  refine (mem_usup_iff h hφ h464 hsq hα hαβ hψ ⟨u, hu⟩).mpr fun B hB => ?_
  obtain ⟨t, ht, rfl⟩ := mem_natImage.mp hB
  exact (commute_iff_natVec hψ t ⟨u, hu⟩).mp (hc _ ht)

omit [Fintype F] in
theorem usup_le_uloc' (hfull : IsSL3Full M T L) {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    Usup (puAmalgam h.le) α β ≤ Uloc h.le L α := by
  rw [S4A.usup_eq_commutator_uloc h hfull hα hαβ]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((qv_le_stab_of_adj _ hαβ.symm).trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α))

omit [Fintype F] in
theorem usup_inf_zloc (hfull : IsSL3Full M T L) {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    Usup (puAmalgam h.le) α β ⊓ Zloc h.le L α = ⊥ := by
  rw [eq_bot_iff, ← uloc_inf_zloc h hfull α]
  exact inf_le_inf_right _ (usup_le_uloc' h hfull hα hαβ)

include hφ h464 hsq in
theorem zh_eq_usup_sup_zloc {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    ZH (puAmalgam h.le) β = Usup (puAmalgam h.le) α β ⊔ Zloc h.le L α := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hβH : ¬ IsMVtx 𝔛 β := by have := isMVtx_iff_of_adj _ hαβ; tauto
  apply le_antisymm
  · intro z hz
    obtain ⟨u, hu, ζ, hζ, rfl⟩ := exists_uloc_mul_zloc h hfull hα (zh_le_zm _ hαβ hz)
    refine Subgroup.mul_mem_sup ?_ hζ
    refine mem_usup_of_commute h hφ h464 hsq hα hαβ hu fun t ht => ?_
    have hζc : t * ζ = ζ * t :=
      Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab h hfull hα hζ) t
        (qv_le_stab_of_adj _ hαβ.symm ht)
    have hzc : t * (u * ζ) = (u * ζ) * t :=
      (Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β hz) t ht)
    have e : t * u * ζ = u * t * ζ := by
      calc t * u * ζ = t * (u * ζ) := by group
        _ = u * ζ * t := hzc
        _ = u * (ζ * t) := by group
        _ = u * t * ζ := by rw [← hζc]; group
    exact mul_right_cancel e
  · exact sup_le (h464 α β hα hαβ) (zloc_le_zh h hfull hα hαβ)

include hφ h464 hsq h466 in
theorem mem_qv_of_commute {γ β : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγβ : (puAmalgam h.le).treeGraph.Adj γ β) {y : 𝔘} (hy : y ∈ ZM (puAmalgam h.le) γ)
    (hyβ : y ∉ ZH (puAmalgam h.le) β) {t : 𝔘} (ht : t ∈ Qv (puAmalgam h.le) β)
    (hty : t * y = y * t) : t ∈ Qv (puAmalgam h.le) γ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hγ
  have hT : Qv 𝔛 β ≤ stab 𝔛 γ := qv_le_stab_of_adj _ hγβ.symm
  obtain ⟨h2, -⟩ := fixN_natImage_qv h hφ h464 hsq hγ hγβ hψ
  have heq := natImage_qv_eq_axisGroup h hφ h464 hsq h466 hγ hγβ hψ
  obtain ⟨u, hu, ζ, hζ, rfl⟩ := exists_uloc_mul_zloc h hfull hγ hy
  have hζc : t * ζ = ζ * t :=
    Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab h hfull hγ hζ) t (hT ht)
  have htu : t * u = u * t := by
    have e : t * u * ζ = u * t * ζ := by
      calc t * u * ζ = t * (u * ζ) := by group
        _ = u * ζ * t := hty
        _ = u * (ζ * t) := by group
        _ = u * t * ζ := by rw [← hζc]; group
    exact mul_right_cancel e
  have hnot : natVec hψ ⟨u, hu⟩ ∉ fixN (natImage ψ (Qv 𝔛 β)) := by
    intro hmem
    apply hyβ
    have huU := (mem_usup_iff h hφ h464 hsq hγ hγβ hψ ⟨u, hu⟩).mpr hmem
    exact Subgroup.mul_mem _ (h464 γ β hγ hγβ huU) (zloc_le_zh h hfull hγ hγβ hζ)
  have htA : toSL3 ψ ⟨t, hT ht⟩ ∈ axisGroup (fixN (natImage ψ (Qv 𝔛 β))) := by
    rw [← heq]
    exact mem_natImage.mpr ⟨_, ht, rfl⟩
  have hfix := (commute_iff_natVec hψ ⟨t, hT ht⟩ ⟨u, hu⟩).mp htu
  have h1 := eq_one_of_mem_axisGroup h2 htA hnot hfix
  exact (toSL3_eq_one_iff_mem_qv h hφ hγ hψ _).mp h1

include hφ h464 hsq h466 in
theorem exists_isOddL1_conj {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1)
    {u v : ↥(Uloc h.le L α)} (hu : natVec hψ u ∈ fixN (natImage ψ (Qv (puAmalgam h.le) β)))
    (hv : natVec hψ v ∈ fixN (natImage ψ (Qv (puAmalgam h.le) β))) (hu0 : natVec hψ u ≠ 0)
    (huv : natVec hψ v ∉ F ∙ natVec hψ u) :
    ∃ g : 𝔘, IsOddL1 (puAmalgam h.le) α β g ∧ g * (u : 𝔘) * g⁻¹ = v := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  obtain ⟨h2, hcf⟩ := fixN_natImage_qv h hφ h464 hsq hα hαβ hψ
  set P := fixN (natImage ψ (Qv 𝔛 β)) with hPdef
  obtain ⟨B, hB3, hBP, hBuv⟩ := exists_rot_pair h2 hu hv hu0 huv
  obtain ⟨g₀, hg₀⟩ := toSL3_surjective hψs B
  have h3 : toSL3 ψ (g₀ ^ 3) = 1 := by rw [map_pow, hg₀, hB3]
  obtain ⟨e, he⟩ := pow_two_pow_eq_one_of_toSL3_eq_one h hφ hα hψ _ h3
  set g₁ : ↥(stab 𝔛 α) := g₀ ^ (4 ^ e) with hg₁
  have hg₁3 : g₁ ^ 3 = 1 := by
    rw [hg₁, ← pow_mul, show 4 ^ e * 3 = 3 * 2 ^ e * 2 ^ e by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]; ring, pow_mul, pow_mul, he, one_pow]
  have hB4 : B ^ (4 ^ e) = B := by
    have hmod : 4 ^ e % 3 = 1 := by
      rw [Nat.pow_mod]; norm_num
    conv_lhs => rw [← Nat.div_add_mod (4 ^ e) 3, hmod, pow_add, pow_mul, hB3, one_pow, one_mul,
      pow_one]
  have hψg₁ : toSL3 ψ g₁ = B := by rw [hg₁, map_pow, hg₀, hB4]
  have hBstab : ∀ p ∈ P, ((B : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p ∈ P := fun p hp => by
    have := P.add_mem (hBP p) hp
    rwa [sub_add_cancel] at this
  have hg₁N := mem_normalizer_qv_of_toSL3 h hφ h464 hsq h466 hα hαβ hψ (g := g₁)
    (by rw [hψg₁]; exact hBstab)
  refine ⟨(g₁ : 𝔘), ⟨g₁.2, hg₁N, fun z hz => ?_, ?_⟩, ?_⟩
  ·
    obtain ⟨w, hw, ζ, hζ, rfl⟩ := exists_uloc_mul_zloc h hfull hα hz
    have hζc : ζ * (g₁ : 𝔘) = (g₁ : 𝔘) * ζ :=
      (Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab h hfull hα hζ) _ g₁.2).symm
    have e1 : ⁅w * ζ, (g₁ : 𝔘)⁆ = ⁅w, (g₁ : 𝔘)⁆ := by
      simp only [commutatorElement_def]
      calc w * ζ * (g₁ : 𝔘) * (w * ζ)⁻¹ * (g₁ : 𝔘)⁻¹
          = w * (ζ * (g₁ : 𝔘)) * ζ⁻¹ * w⁻¹ * (g₁ : 𝔘)⁻¹ := by group
        _ = w * (g₁ : 𝔘) * w⁻¹ * (g₁ : 𝔘)⁻¹ := by rw [hζc]; group
    rw [e1]
    have hUn := stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α
    have hcU : ⁅w, (g₁ : 𝔘)⁆ ∈ Uloc h.le L α :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (le_trans (fun x hx => hx)
        (show Subgroup.zpowers (g₁ : 𝔘) ≤ Subgroup.normalizer (Uloc h.le L α : Set 𝔘) from
          (Subgroup.zpowers_le).mpr (hUn g₁.2)))
        (Subgroup.commutator_mem_commutator hw (Subgroup.mem_zpowers _))
    have hmem : natVec hψ ⟨_, hcU⟩ ∈ P := by
      rw [natVec_commutator hψ g₁ ⟨w, hw⟩ ⟨_, hcU⟩ rfl, hψg₁]
      have := hBP (natVec hψ ⟨w, hw⟩)
      rw [← neg_sub]
      exact P.neg_mem this
    exact h464 α β hα hαβ ((mem_usup_iff h hφ h464 hsq hα hαβ hψ ⟨_, hcU⟩).mpr hmem)
  ·
    have hdvd : orderOf (g₁ : 𝔘) ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← Subgroup.coe_pow, hg₁3, Subgroup.coe_one]
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1 <;> rw [h1] <;> decide
  ·
    have hUn := stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α
    have hm : (g₁ : 𝔘) * u * (g₁ : 𝔘)⁻¹ ∈ Uloc h.le L α :=
      (Subgroup.mem_normalizer_iff.mp (hUn g₁.2) _).mp u.2
    have hnat := natVec_conj hψ g₁ u ⟨_, hm⟩ rfl
    rw [hψg₁, hBuv] at hnat
    have := natVec_injective hψ hnat
    exact congrArg Subtype.val this

include hφ h464 hsq h466 in
theorem eq_bot_or_eq_usup {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) {X : Subgroup 𝔘}
    (hX : X ≤ Usup (puAmalgam h.le) α β)
    (hinv : ∀ g : 𝔘, IsOddL1 (puAmalgam h.le) α β g → ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    X = ⊥ ∨ X = Usup (puAmalgam h.le) α β := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hα
  obtain ⟨h2, -⟩ := fixN_natImage_qv h hφ h464 hsq hα hαβ hψ
  set P := fixN (natImage ψ (Qv 𝔛 β)) with hPdef
  have hUU := usup_le_uloc' h hfull hα hαβ
  rcases Subgroup.bot_or_exists_ne_one X with hb | ⟨a, haX, ha1⟩
  · exact Or.inl hb
  right
  refine le_antisymm hX fun b hb' => ?_
  have haU : (a : 𝔘) ∈ Uloc h.le L α := hUU (hX haX)
  set u : ↥(Uloc h.le L α) := ⟨a, haU⟩ with hudef
  have huP : natVec hψ u ∈ P := (mem_usup_iff h hφ h464 hsq hα hαβ hψ u).mp (hX haX)
  have hu0 : natVec hψ u ≠ 0 := by
    intro h0
    apply ha1
    have : u = 1 := natVec_injective hψ (by rw [h0, natVec_one])
    exact congrArg Subtype.val this
  have step : ∀ x : ↥(Uloc h.le L α), (x : 𝔘) ∈ X → natVec hψ x ∈ P → natVec hψ x ≠ 0 →
      ∀ y : ↥(Uloc h.le L α), natVec hψ y ∈ P → natVec hψ y ∉ F ∙ natVec hψ x →
        (y : 𝔘) ∈ X := by
    intro x hxX hxP hx0 y hyP hyx
    obtain ⟨g, hg, hgxy⟩ := exists_isOddL1_conj h hφ h464 hsq h466 hα hαβ hψs hψ hxP hyP hx0 hyx
    rw [← hgxy]
    exact hinv g hg _ hxX
  have hbU : b ∈ Uloc h.le L α := hUU hb'
  set v : ↥(Uloc h.le L α) := ⟨b, hbU⟩ with hvdef
  have hvP : natVec hψ v ∈ P := (mem_usup_iff h hφ h464 hsq hα hαβ hψ v).mp hb'
  by_cases hvu : natVec hψ v ∈ F ∙ natVec hψ u
  · by_cases hv0 : natVec hψ v = 0
    · have : v = 1 := natVec_injective hψ (by rw [hv0, natVec_one])
      have hb1 : b = 1 := congrArg Subtype.val this
      rw [hb1]
      exact X.one_mem
    obtain ⟨w, hwP, hwu⟩ := exists_mem_not_mem_span h2 (natVec hψ u)
    obtain ⟨c, hc⟩ := natVec_surjective hψ w
    have hcX : (c : 𝔘) ∈ X := step u haX huP hu0 c (by rw [hc]; exact hwP) (by rw [hc]; exact hwu)
    have hw0 : natVec hψ c ≠ 0 := by
      rw [hc]
      intro h0
      exact hwu (by rw [h0]; exact Submodule.zero_mem _)
    refine step c hcX (by rw [hc]; exact hwP) hw0 v hvP fun hvc => ?_
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hvu
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hvc
    rw [hc] at ht
    by_cases ht0 : t = 0
    · apply hv0
      rw [← ht, ht0, zero_smul]
    · apply hwu
      have : w = t⁻¹ • (s • natVec hψ u) := by rw [hs, ← ht, smul_smul, inv_mul_cancel₀ ht0,
        one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · exact step u haX huP hu0 v hvP hvu

include hφ h464 hsq h466 in
theorem exists_isOddL1_conj_ne {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) {a : 𝔘} (ha : a ∈ Usup (puAmalgam h.le) α β)
    (ha1 : a ≠ 1) :
    ∃ g : 𝔘, IsOddL1 (puAmalgam h.le) α β g ∧ g * a * g⁻¹ ∈ Usup (puAmalgam h.le) α β ∧
      g * a * g⁻¹ ≠ a := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hα
  obtain ⟨h2, -⟩ := fixN_natImage_qv h hφ h464 hsq hα hαβ hψ
  have haU : a ∈ Uloc h.le L α := usup_le_uloc' h hfull hα hαβ ha
  set u : ↥(Uloc h.le L α) := ⟨a, haU⟩ with hudef
  have huP := (mem_usup_iff h hφ h464 hsq hα hαβ hψ u).mp ha
  have hu0 : natVec hψ u ≠ 0 := by
    intro h0
    apply ha1
    have : u = 1 := natVec_injective hψ (by rw [h0, natVec_one])
    exact congrArg Subtype.val this
  obtain ⟨w, hwP, hwu⟩ := exists_mem_not_mem_span h2 (natVec hψ u)
  obtain ⟨c, hc⟩ := natVec_surjective hψ w
  obtain ⟨g, hg, hgc⟩ := exists_isOddL1_conj h hφ h464 hsq h466 hα hαβ hψs hψ huP
    (by rw [hc]; exact hwP) hu0 (by rw [hc]; exact hwu)
  refine ⟨g, hg, ?_, ?_⟩
  · rw [show g * a * g⁻¹ = (c : 𝔘) from hgc]
    exact (mem_usup_iff h hφ h464 hsq hα hαβ hψ c).mpr (by rw [hc]; exact hwP)
  · rw [show g * a * g⁻¹ = (c : 𝔘) from hgc]
    intro hca
    apply hwu
    have : c = u := Subtype.ext hca
    rw [← hc, this]
    exact Submodule.mem_span_singleton_self _

end Loc

end CFSG.Quasithin.MS93.S46
