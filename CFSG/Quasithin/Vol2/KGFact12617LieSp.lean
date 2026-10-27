module

public import CFSG.Quasithin.Vol2.KGFact12617LieW
public import CFSG.LieType.BorelTits.Symplectic

public section

namespace CFSG.Quasithin.H13.KG12617Lie

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank Module
open scoped commutatorElement

section TwoStep

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] {H : Type*} [Group H]
  (ρ : H →* Module.End K V)

theorem rep_sub_add_smul (g : H) (m v : V) (c : K) :
    ρ g (m + c • v) - (m + c • v) = (ρ g m - m) + c • (ρ g v - v) := by
  rw [map_add, map_smul, smul_sub]
  abel

theorem exists_mid [Finite V] [CharP K 2] (D : Subgroup H) (hD : IsPGroup 2 ↥D)
    {A C : Submodule K V} (hAC : A ≤ C) (hdim : finrank K C ≤ finrank K A + 2)
    (hA : ∀ g ∈ D, ∀ v ∈ A, ρ g v ∈ A) (hC : ∀ g ∈ D, ∀ v ∈ C, ρ g v ∈ C) :
    ∃ M : Submodule K V, A ≤ M ∧ M ≤ C ∧ (∀ g ∈ D, ∀ v ∈ C, ρ g v - v ∈ M) ∧
      ∀ g ∈ D, ∀ v ∈ M, ρ g v - v ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : FiniteDimensional K V := Module.Finite.of_finite
  rcases eq_or_lt_of_le hAC with hAC' | hAC'
  · refine ⟨A, le_rfl, hAC, fun g hg v hv => ?_, fun g hg v hv => A.sub_mem (hA g hg v hv) hv⟩
    rw [← hAC'] at hv
    exact A.sub_mem (hA g hg v hv) hv
  obtain ⟨v₀, hv₀C, hv₀A, hv₀⟩ := exists_mem_notMem_forall_sub_mem ρ 2 D hD hAC' hA hC
  set M := A ⊔ K ∙ v₀ with hM
  have hMA : ∀ g ∈ D, ∀ v ∈ M, ρ g v - v ∈ A := by
    intro g hg v hv
    obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [rep_sub_add_smul]
    exact A.add_mem (A.sub_mem (hA g hg a ha) ha) (A.smul_mem c (hv₀ g hg))
  have hMst : ∀ g ∈ D, ∀ v ∈ M, ρ g v ∈ M := fun g hg v hv => by
    have h : ρ g v = (ρ g v - v) + v := by abel
    rw [h]
    exact M.add_mem (Submodule.mem_sup_left (hMA g hg v hv)) hv
  have hMC : M ≤ C := sup_le hAC ((Submodule.span_singleton_le_iff_mem _ _).2 hv₀C)
  have hAM : A < M := lt_of_le_of_ne le_sup_left fun h =>
    hv₀A (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self v₀))
  rcases eq_or_lt_of_le hMC with hMC' | hMC'
  · refine ⟨M, le_sup_left, hMC, fun g hg v hv => ?_, hMA⟩
    rw [← hMC'] at hv
    exact M.sub_mem (hMst g hg v hv) hv
  obtain ⟨v₁, hv₁C, hv₁M, hv₁⟩ := exists_mem_notMem_forall_sub_mem ρ 2 D hD hMC' hMst hC
  have hM'C : M ⊔ K ∙ v₁ ≤ C := sup_le hMC ((Submodule.span_singleton_le_iff_mem _ _).2 hv₁C)
  have hMM' : M < M ⊔ K ∙ v₁ := lt_of_le_of_ne le_sup_left fun h =>
    hv₁M (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self v₁))
  have hM'eq : M ⊔ K ∙ v₁ = C := by
    apply Submodule.eq_of_le_of_finrank_le hM'C
    have h1 := Submodule.finrank_lt_finrank_of_lt hAM
    have h2 := Submodule.finrank_lt_finrank_of_lt hMM'
    omega
  refine ⟨M, le_sup_left, hMC, fun g hg v hv => ?_, hMA⟩
  rw [← hM'eq] at hv
  obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  rw [rep_sub_add_smul]
  exact M.add_mem (M.sub_mem (hMst g hg m hm) hm) (M.smul_mem c (hv₁ g hg))

theorem commutator_sub_mem [Finite V] [CharP K 2] (D : Subgroup H) (hD : IsPGroup 2 ↥D)
    {A C : Submodule K V} (hAC : A ≤ C) (hdim : finrank K C ≤ finrank K A + 2)
    (hA : ∀ g ∈ D, ∀ v ∈ A, ρ g v ∈ A) (hC : ∀ g ∈ D, ∀ v ∈ C, ρ g v ∈ C) {x y : H}
    (hx : x ∈ D) (hy : y ∈ D) {v : V} (hv : v ∈ C) : ρ ⁅x, y⁆ v - v ∈ A := by
  obtain ⟨M, -, -, hCM, hMA⟩ := exists_mid ρ D hD hAC hdim hA hC
  set u := ρ (y * x)⁻¹ v with hu
  have huC : u ∈ C := hC _ (D.inv_mem (D.mul_mem hy hx)) v hv
  have h1 : ρ ⁅x, y⁆ v = ρ x (ρ y u) := by
    have : ⁅x, y⁆ = x * y * (y * x)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [this, map_mul, map_mul]
    rfl
  have h2 : ρ y (ρ x u) = v := by
    rw [hu, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  have key : ρ ⁅x, y⁆ v - v =
      (ρ x (ρ y u - u) - (ρ y u - u)) - (ρ y (ρ x u - u) - (ρ x u - u)) := by
    rw [h1]
    conv_lhs => rw [← h2]
    simp only [map_sub]
    abel
  rw [key]
  exact A.sub_mem (hMA x hx _ (hCM y hy u huC)) (hMA y hy _ (hCM x hx u huC))

end TwoStep

section Sp4

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem le_perp_of_finrank_eq_one {L : Submodule F (Fin 2 ⊕ Fin 2 → F)}
    (hL : finrank F L = 1) : L ≤ (spForm 2 F).perp L := by
  obtain ⟨u, -, hu⟩ := finrank_eq_one_iff'.1 hL
  intro a ha b hb
  obtain ⟨c, hc⟩ := hu ⟨a, ha⟩
  obtain ⟨d, hd⟩ := hu ⟨b, hb⟩
  have hc' : c • (u : Fin 2 ⊕ Fin 2 → F) = a := by simpa using congrArg Subtype.val hc
  have hd' : d • (u : Fin 2 ⊕ Fin 2 → F) = b := by simpa using congrArg Subtype.val hd
  rw [← hc', ← hd', (spForm 2 F).smul_left, (spForm 2 F).smul_right, spForm_self, mul_zero,
    mul_zero]

theorem commutator_mem_of_mem {G : Type*} [Group G] (S : Subgroup G) {x y : G} (hx : x ∈ S)
    (hy : y ∈ S) : ⁅x, y⁆ ∈ S := by
  rw [commutatorElement_def]
  exact S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy)

theorem false_of_flag {B : Subgroup ↥(StatedSp 2 F)}
    (hBiso : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6)))
    (Fl : ℕ → Submodule F (Fin 2 ⊕ Fin 2 → F)) (h0 : Fl 0 = ⊥) (h3 : Fl 3 = ⊤)
    (hsteps : ∀ k, Fl k ≤ Fl (k + 1) ∧ finrank F (Fl (k + 1)) ≤ finrank F (Fl k) + 2)
    (hstab : ∀ b ∈ B, ∀ k, ∀ v ∈ Fl k, natRep (StatedSp 2 F) b v ∈ Fl k) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := natRep (StatedSp 2 F)
  have hBst : B ≤ flagStab ρ Fl := fun b hb k v hv =>
    ⟨hstab b hb k v hv, hstab b⁻¹ (B.inv_mem hb) k v hv⟩
  refine false_of_commutator_mem hBiso
    (isPGroup_flagKernel ρ 2 (natRep_injective _) h0 h3)
    (hBst.trans (flagStab_le_normalizer_flagKernel ρ Fl)) fun D hDB hD x hx y hy => ?_
  refine ⟨commutator_mem_of_mem _ (hBst (hDB hx)) (hBst (hDB hy)), fun k v hv => ?_⟩
  exact commutator_sub_mem ρ D hD (hsteps k).1 (hsteps k).2
    (fun g hg w hw => hstab g (hDB hg) k w hw) (fun g hg w hw => hstab g (hDB hg) (k + 1) w hw)
    hx hy hv

omit [Finite F] [CharP F 2] in
theorem finrank_sp4 : finrank F (Fin 2 ⊕ Fin 2 → F) = 4 := by
  rw [finrank_fintype_fun_eq_card]
  rfl

@[expose] def chain4 (L₁ L₂ : Submodule F (Fin 2 ⊕ Fin 2 → F)) :
    ℕ → Submodule F (Fin 2 ⊕ Fin 2 → F)
  | 0 => ⊥
  | 1 => L₁
  | 2 => L₂
  | _ + 3 => ⊤

theorem false_of_chain {B : Subgroup ↥(StatedSp 2 F)}
    (hBiso : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6)))
    {L₁ L₂ : Submodule F (Fin 2 ⊕ Fin 2 → F)} (h12 : L₁ ≤ L₂) (hd1 : finrank F L₁ ≤ 2)
    (hd2 : finrank F L₂ ≤ finrank F L₁ + 2) (hd3 : 2 ≤ finrank F L₂)
    (hs1 : ∀ b ∈ B, ∀ v ∈ L₁, natRep (StatedSp 2 F) b v ∈ L₁)
    (hs2 : ∀ b ∈ B, ∀ v ∈ L₂, natRep (StatedSp 2 F) b v ∈ L₂) : False := by
  refine false_of_flag hBiso (chain4 L₁ L₂) rfl rfl (fun k => ?_) (fun b hb k v hv => ?_)
  · rcases k with _ | _ | _ | k
    · exact ⟨bot_le, by rw [show chain4 L₁ L₂ 0 = ⊥ from rfl, finrank_bot]; exact hd1⟩
    · exact ⟨h12, hd2⟩
    · refine ⟨le_top, ?_⟩
      show finrank F ↥(⊤ : Submodule F (Fin 2 ⊕ Fin 2 → F)) ≤ finrank F L₂ + 2
      rw [finrank_top, finrank_sp4]
      omega
    · exact ⟨le_top, by
        show finrank F ↥(⊤ : Submodule F (Fin 2 ⊕ Fin 2 → F)) ≤
          finrank F ↥(⊤ : Submodule F (Fin 2 ⊕ Fin 2 → F)) + 2
        omega⟩
  · rcases k with _ | _ | _ | k
    · have hv0 : v = 0 := (Submodule.mem_bot F).1 hv
      rw [hv0, map_zero]
      exact Submodule.zero_mem _
    · exact hs1 b hb v hv
    · exact hs2 b hb v hv
    · exact Submodule.mem_top

theorem false_of_normalizes_sp4 {B W : Subgroup ↥(StatedSp 2 F)}
    (hBiso : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6))) (hW : W ≠ ⊥)
    (hW2 : IsPGroup 2 ↥W) (hBW : B ≤ Subgroup.normalizer (W : Set ↥(StatedSp 2 F))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := natRep (StatedSp 2 F) with hρ
  set U := fixFlag ρ W 1 with hU
  have hUst : ∀ b ∈ B, ∀ v ∈ U, ρ b v ∈ U := fun b hb v hv =>
    ((normalizer_le_flagStab_fixFlag ρ W) (hBW hb) 1 v hv).1
  have hUinv : ∀ b ∈ B, ∀ v ∈ U, ρ b⁻¹ v ∈ U := fun b hb v hv => hUst _ (B.inv_mem hb) v hv
  have hUne : U ≠ ⊥ := by
    obtain ⟨v, hv0, hv⟩ := exists_fixed_ne_zero ρ 2 W hW2
    intro hbot
    have hvU : v ∈ U := by
      rw [hU, mem_fixFlag_succ]
      intro g hg
      rw [hv g hg, sub_self]
      exact Submodule.zero_mem _
    rw [hbot, Submodule.mem_bot] at hvU
    exact hv0 hvU
  have hUtop : U ≠ ⊤ := by
    intro htop
    apply hW
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    apply natRep_injective (StatedSp 2 F)
    rw [map_one]
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ U := htop ▸ Submodule.mem_top
    rw [hU, mem_fixFlag_succ] at hv
    have h := hv w hw
    rw [fixFlag_zero, Submodule.mem_bot, sub_eq_zero] at h
    rw [h, Module.End.one_apply]
  have hd0 : finrank F U ≠ 0 := fun h => hUne (Submodule.finrank_eq_zero.1 h)
  have hd4 : finrank F U ≠ 4 := fun h =>
    hUtop (Submodule.eq_top_of_finrank_eq (h.trans finrank_sp4.symm))
  have hdle : finrank F U ≤ 4 := finrank_sp4 (F := F) ▸ Submodule.finrank_le U
  have hiso := isIsometric_natRep_statedSp (n := 2) (K := F)
  have hperp := (spForm 2 F).finrank_perp U
  rw [finrank_sp4] at hperp
  have hperpst : ∀ (Lw : Submodule F (Fin 2 ⊕ Fin 2 → F)),
      (∀ b ∈ B, ∀ v ∈ Lw, ρ b v ∈ Lw) → ∀ b ∈ B, ∀ v ∈ (spForm 2 F).perp Lw,
        ρ b v ∈ (spForm 2 F).perp Lw := fun Lw hLw b hb v hv =>
    hiso.apply_mem_perp_of_forall (fun w hw => hLw _ (B.inv_mem hb) w hw) hv
  by_cases h2 : finrank F U = 2
  · exact false_of_chain hBiso le_rfl h2.le (by omega) h2.ge hUst hUst
  ·
    obtain ⟨L, hL1, hLst⟩ : ∃ L : Submodule F (Fin 2 ⊕ Fin 2 → F), finrank F L = 1 ∧
        ∀ b ∈ B, ∀ v ∈ L, ρ b v ∈ L := by
      by_cases h1 : finrank F U = 1
      · exact ⟨U, h1, hUst⟩
      · exact ⟨(spForm 2 F).perp U, by omega, hperpst U hUst⟩
    have hLp := (spForm 2 F).finrank_perp L
    rw [finrank_sp4, hL1] at hLp
    exact false_of_chain hBiso (le_perp_of_finrank_eq_one hL1) (by omega) (by omega) (by omega)
      hLst (hperpst L hLst)

end Sp4

end CFSG.Quasithin.H13.KG12617Lie
