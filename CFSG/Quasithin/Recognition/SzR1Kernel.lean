module

public import CFSG.Quasithin.Recognition.SzR1FamCenter
public import CFSG.Quasithin.Recognition.SzR1GramPar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped commutatorElement

namespace SzR1

section Aux

variable {G : Type} [Group G]

theorem mem_normalizer_of_conjSub_eq' {x : G} {H : Subgroup G} (h : conjSub x H = H) :
    x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : x * y * x⁻¹ ∈ conjSub x H := mul_mem_conjSub hy
    rwa [h] at this
  · intro hy
    have h1 : x * y * x⁻¹ ∈ conjSub x H := by rwa [h]
    have := mem_conjSub.mp h1
    simpa [mul_assoc] using this

theorem S_le_normalizer_vBeta (K1 L2 S Zs : Subgroup G) :
    S ≤ Subgroup.normalizer (vBeta K1 L2 S Zs : Set G) := fun _ hs =>
  le_normalizer_conjClosure (conjClosure Zs L2) (K1 ⊔ S) (Subgroup.mem_sup_right hs)

@[expose] def conjHom (K1 L2 S Zs : Subgroup G) {s : G} (hs : s ∈ S) :
    ↥(vBeta K1 L2 S Zs) →* ↥(vBeta K1 L2 S Zs) :=
  MonoidHom.mk'
    (fun x => ⟨s * (x : G) * s⁻¹,
      (Subgroup.mem_normalizer_iff.mp (S_le_normalizer_vBeta K1 L2 S Zs hs) _).mp x.2⟩)
    (fun x y => Subtype.ext (by
      show s * ((x : G) * (y : G)) * s⁻¹ = s * (x : G) * s⁻¹ * (s * (y : G) * s⁻¹)
      group))

end Aux

namespace FamCtx

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  (C : FamCtx K1 L2 S Zs Ω)

include C

theorem exists_conjSub_Vf_of_mem_S {s : G} (hs : s ∈ S) (ω : Ω) :
    ∃ ω' : Ω, conjSub s (C.D.Vf (conjClosure Zs L2) ω) = C.D.Vf (conjClosure Zs L2) ω' := by
  have hsK : s ∈ Subgroup.normalizer (K1 : Set G) := C.hSK hs
  have hk' : s * (C.D.kf ω : G) * s⁻¹ ∈ K1 :=
    (Subgroup.mem_normalizer_iff.mp hsK _).mp (C.D.kf ω).2
  obtain ⟨k', hk'e⟩ : ∃ k' : ↥K1, (k' : G) = s * (C.D.kf ω : G) * s⁻¹ := ⟨⟨_, hk'⟩, rfl⟩
  refine ⟨C.D.act k' C.D.pt, ?_⟩
  rw [← C.D.conjSub_V C.hVn k', hk'e]
  unfold FamData.Vf
  calc conjSub s (conjSub (C.D.kf ω : G) (conjClosure Zs L2))
      = conjSub (s * (C.D.kf ω : G)) (conjClosure Zs L2) := (conjSub_mul _ _ _).symm
    _ = conjSub ((s * (C.D.kf ω : G) * s⁻¹) * s) (conjClosure Zs L2) := by
        congr 1
        group
    _ = conjSub (s * (C.D.kf ω : G) * s⁻¹) (conjSub s (conjClosure Zs L2)) :=
        conjSub_mul _ _ _
    _ = conjSub (s * (C.D.kf ω : G) * s⁻¹) (conjClosure Zs L2) := by
        rw [F7.conjSub_eq_of_mem_normalizer (C.hSV hs)]

theorem exists_conjSub_Vf_of_mem_sup {g : G} (hg : g ∈ K1 ⊔ S) (ω : Ω) :
    ∃ ω' : Ω, conjSub g (C.D.Vf (conjClosure Zs L2) ω) = C.D.Vf (conjClosure Zs L2) ω' := by
  obtain ⟨k, hk, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes C.hSK).mp hg
  obtain ⟨ω₁, h1⟩ := C.exists_conjSub_Vf_of_mem_S hs ω
  refine ⟨C.D.act ⟨k, hk⟩ ω₁, ?_⟩
  rw [conjSub_mul, h1]
  exact C.D.conjSub_Vf C.hVn ⟨k, hk⟩ ω₁

@[expose] def kerM : Subgroup G :=
  (K1 ⊔ S) ⊓ ⨅ ω, Subgroup.normalizer (C.D.Vf (conjClosure Zs L2) ω : Set G)

theorem mem_kerM {x : G} : x ∈ C.kerM ↔ x ∈ K1 ⊔ S ∧
    ∀ ω, conjSub x (C.D.Vf (conjClosure Zs L2) ω) = C.D.Vf (conjClosure Zs L2) ω := by
  unfold kerM
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf]
  exact and_congr_right fun _ => forall_congr' fun ω =>
    ⟨F7.conjSub_eq_of_mem_normalizer, mem_normalizer_of_conjSub_eq'⟩

theorem kerM_le_sup : C.kerM ≤ K1 ⊔ S := fun _ hx => (C.mem_kerM.mp hx).1

theorem sup_le_normalizer_kerM : K1 ⊔ S ≤ Subgroup.normalizer (C.kerM : Set G) := by
  have key : ∀ g ∈ K1 ⊔ S, ∀ x ∈ C.kerM, g * x * g⁻¹ ∈ C.kerM := by
    intro g hg x hx
    rw [mem_kerM] at hx ⊢
    refine ⟨(K1 ⊔ S).mul_mem ((K1 ⊔ S).mul_mem hg hx.1) ((K1 ⊔ S).inv_mem hg), fun ω => ?_⟩
    obtain ⟨ω₁, h1⟩ := C.exists_conjSub_Vf_of_mem_sup ((K1 ⊔ S).inv_mem hg) ω
    rw [show g * x * g⁻¹ = g * (x * g⁻¹) from mul_assoc _ _ _, conjSub_mul, conjSub_mul, h1,
      hx.2 ω₁, ← h1, conjSub_inv_conjSub]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  simpa [mul_assoc] using key g⁻¹ ((K1 ⊔ S).inv_mem hg) _ hx

theorem sup_le_centralizer_Zs : K1 ⊔ S ≤ Subgroup.centralizer (Zs : Set G) :=
  sup_le C.h.K1_cent_Z (F112J2.S_le_centralizer_Z C.h)

theorem vBeta_le_kerM : vBeta K1 L2 S Zs ≤ C.kerM := by
  intro w hw
  rw [mem_kerM]
  refine ⟨C.U_le_sup hw, fun ω => ?_⟩
  have hle : ∀ u ∈ vBeta K1 L2 S Zs, conjSub u (C.D.Vf (conjClosure Zs L2) ω) ≤
      C.D.Vf (conjClosure Zs L2) ω := by
    intro u hu x hx
    have hy : u⁻¹ * x * u ∈ C.D.Vf (conjClosure Zs L2) ω := mem_conjSub.mp hx
    have hyW : u⁻¹ * x * u ∈ vBeta K1 L2 S Zs := C.Vf_le_U ω hy
    have hc : u * (u⁻¹ * x * u) * u⁻¹ * (u⁻¹ * x * u)⁻¹ ∈ Zs := C.U_comm_mem hu hyW
    have e : x = (u * (u⁻¹ * x * u) * u⁻¹ * (u⁻¹ * x * u)⁻¹) * (u⁻¹ * x * u) := by group
    rw [e]
    exact (C.D.Vf (conjClosure Zs L2) ω).mul_mem (C.Zs_le_Vf ω hc) hy
  apply le_antisymm (hle w hw)
  exact (le_conjSub_iff w).mpr (hle w⁻¹ ((vBeta K1 L2 S Zs).inv_mem hw))

theorem kerM_conj_mem {m : G} (hm : m ∈ C.kerM) {x : G} (hx : x ∈ vBeta K1 L2 S Zs) :
    ∃ c ∈ Zs, m * x * m⁻¹ = c * x := by
  obtain ⟨z₀, hz₀, hne⟩ := C.exists_ne_one
  have hmc : m ∈ Subgroup.centralizer (Zs : Set G) :=
    C.sup_le_centralizer_Zs (C.kerM_le_sup hm)
  rw [C.U_eq_closure hz₀ hne] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨ω, rfl⟩
    · refine ⟨1, Zs.one_mem, ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hmc x hz₀
      rw [one_mul, ← this]
      group
    · have hmV : conjSub m (C.D.Vf (conjClosure Zs L2) ω) = C.D.Vf (conjClosure Zs L2) ω :=
        (C.mem_kerM.mp hm).2 ω
      have h1 : m * C.zf ω * m⁻¹ ∈ C.D.Vf (conjClosure Zs L2) ω := by
        rw [← hmV]
        exact mul_mem_conjSub (C.zf_mem ω)
      rcases C.Vf_eq h1 with h2 | h2
      · exfalso
        apply C.zf_not_mem ω
        have h3 := Subgroup.mem_centralizer_iff.mp hmc _ h2
        have h4 : C.zf ω = m * C.zf ω * m⁻¹ := by
          calc C.zf ω = m⁻¹ * ((m * C.zf ω * m⁻¹) * m) := by group
            _ = m⁻¹ * (m * (m * C.zf ω * m⁻¹)) := by rw [h3]
            _ = m * C.zf ω * m⁻¹ := by group
        rw [h4]
        exact h2
      · refine ⟨(C.zf ω)⁻¹ * (m * C.zf ω * m⁻¹), h2, ?_⟩
        have hc := C.Zs_central (C.zf_mem_U ω) h2
        calc m * C.zf ω * m⁻¹ = C.zf ω * ((C.zf ω)⁻¹ * (m * C.zf ω * m⁻¹)) := by group
          _ = ((C.zf ω)⁻¹ * (m * C.zf ω * m⁻¹)) * C.zf ω := hc
  | one => exact ⟨1, Zs.one_mem, by simp⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨c, hc, hcx⟩ := ihx
    obtain ⟨c', hc', hcy⟩ := ihy
    have hxU : x ∈ vBeta K1 L2 S Zs := by
      rw [C.U_eq_closure hz₀ hne]
      exact hx
    refine ⟨c * c', Zs.mul_mem hc hc', ?_⟩
    have hxc : x * c' = c' * x := C.Zs_central hxU hc'
    calc m * (x * y) * m⁻¹ = (m * x * m⁻¹) * (m * y * m⁻¹) := by group
      _ = (c * x) * (c' * y) := by rw [hcx, hcy]
      _ = c * (x * c') * y := by group
      _ = c * (c' * x) * y := by rw [hxc]
      _ = (c * c') * (x * y) := by group
  | inv x hx ih =>
    obtain ⟨c, hc, hcx⟩ := ih
    have hxU : x ∈ vBeta K1 L2 S Zs := by
      rw [C.U_eq_closure hz₀ hne]
      exact hx
    refine ⟨c⁻¹, Zs.inv_mem hc, ?_⟩
    have hxc : x * c = c * x := C.Zs_central hxU hc
    calc m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ := by group
      _ = (c * x)⁻¹ := by rw [hcx]
      _ = (x * c)⁻¹ := by rw [hxc]
      _ = c⁻¹ * x⁻¹ := by group

theorem commutator_kerM_vBeta_mem {m : G} (hm : m ∈ C.kerM) {x : G}
    (hx : x ∈ vBeta K1 L2 S Zs) : m * x * m⁻¹ * x⁻¹ ∈ Zs := by
  obtain ⟨c, hc, hcx⟩ := C.kerM_conj_mem hm hx
  rw [hcx]
  simpa using hc

theorem commutator_kerM_vBeta_le : ⁅C.kerM, vBeta K1 L2 S Zs⁆ ≤ Zs := by
  rw [Subgroup.commutator_le]
  intro m hm x hx
  rw [commutatorElement_def]
  exact C.commutator_kerM_vBeta_mem hm hx

theorem Vf_pt : C.D.Vf (conjClosure Zs L2) C.D.pt = conjClosure Zs L2 := by
  have h := (C.D.stab (C.D.kf C.D.pt)).mp (C.D.kf_spec C.D.pt)
  exact F7.conjSub_eq_of_mem_normalizer (C.hVn h)

theorem exists_sigma {s : G} (hs : s ∈ S) :
    ∃ (σ : Ω → Ω) (c : Ω → G), (∀ i, c i ∈ Zs) ∧
      (∀ i, s * C.zf i * s⁻¹ = C.zf (σ i) * c i) ∧
      ∀ i, conjSub s (C.D.Vf (conjClosure Zs L2) i) = C.D.Vf (conjClosure Zs L2) (σ i) := by
  choose σ hσ using fun i => C.exists_conjSub_Vf_of_mem_S hs i
  have hc : ∀ i, ∃ c ∈ Zs, s * C.zf i * s⁻¹ = C.zf (σ i) * c := by
    intro i
    have h1 : s * C.zf i * s⁻¹ ∈ C.D.Vf (conjClosure Zs L2) (σ i) := by
      rw [← hσ i]
      exact mul_mem_conjSub (C.zf_mem i)
    have hsc := Subgroup.mem_centralizer_iff.mp (F112J2.S_le_centralizer_Z C.h hs)
    rcases C.Vf_eq h1 with h2 | h2
    · exfalso
      apply C.zf_not_mem i
      have h3 := hsc _ h2
      have h4 : C.zf i = s * C.zf i * s⁻¹ := by
        calc C.zf i = s⁻¹ * ((s * C.zf i * s⁻¹) * s) := by group
          _ = s⁻¹ * (s * (s * C.zf i * s⁻¹)) := by rw [h3]
          _ = s * C.zf i * s⁻¹ := by group
      rw [h4]
      exact h2
    · exact ⟨_, h2, by group⟩
  choose c hcZ hcE using hc
  exact ⟨σ, c, hcZ, hcE, hσ⟩

theorem exists_pow_zU {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) {x : G} (hx : x ∈ Zs) :
    ∃ e : ℕ, x = (C.cm i₀ j₀) ^ e := by
  have hz₀ : C.cm i₀ j₀ ∈ Zs := C.cm_mem i₀ j₀
  have hne : C.cm i₀ j₀ ≠ 1 := C.cm_ne_one hij
  have hx' : x ∈ Subgroup.zpowers (C.cm i₀ j₀) := by
    rw [← C.Zs_eq_zpowers hz₀ hne]
    exact hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
  have hsq : C.cm i₀ j₀ ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact C.Zs_sq hz₀
  have e1 : C.cm i₀ j₀ ^ k = C.cm i₀ j₀ ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, hsq, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · exact ⟨0, by rw [e1, h0]; simp⟩
  · exact ⟨1, by rw [e1, h1]; simp⟩

section Fix

variable [DecidableEq Ω]

theorem mem_kerM_of_fix {i₀ j₀ : Ω} (hij : i₀ ≠ j₀)
    (h4 : ∀ i : Ω, i ≠ C.D.pt → ∃ j k : Ω, j ≠ C.D.pt ∧ k ≠ C.D.pt ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k)
    {s : G} (hs : s ∈ S)
    (hfix : ∀ i j : Ω, i ≠ C.D.pt → j ≠ C.D.pt → i ≠ j →
      ∃ c ∈ Zs, s * (C.zf i * C.zf j) * s⁻¹ = c * (C.zf i * C.zf j)) :
    s ∈ C.kerM := by
  rw [mem_kerM]
  refine ⟨Subgroup.mem_sup_right hs, fun ω => ?_⟩
  obtain ⟨σ, c, hcZ, hcE, hσ⟩ := C.exists_sigma hs
  by_cases hω : ω = C.D.pt
  · subst hω
    rw [C.Vf_pt]
    exact F7.conjSub_eq_of_mem_normalizer (C.hSV hs)
  · have hσω : σ ω = ω := by
      obtain ⟨j, k, hj, hk, hωj, hωk, hjk⟩ := h4 ω hω
      have hG := C.gramRel hij
      have hz : C.zU i₀ j₀ ≠ 1 := fun h => C.cm_ne_one hij (congrArg Subtype.val h)
      have hpair : ∀ j : Ω, j ≠ C.D.pt → ω ≠ j →
          ∃ d : ↥(vBeta K1 L2 S Zs), (∀ g, d * g = g * d) ∧
            conjHom K1 L2 S Zs hs (C.wU ω * C.wU j) = C.wU ω * C.wU j * d := by
        intro j hj hωj
        obtain ⟨d, hd, hde⟩ := hfix ω j hω hj hωj
        have hu : C.zf ω * C.zf j ∈ vBeta K1 L2 S Zs :=
          (vBeta K1 L2 S Zs).mul_mem (C.zf_mem_U ω) (C.zf_mem_U j)
        refine ⟨⟨d, F112J2.Zs_le_vBeta K1 L2 S Zs hd⟩,
          fun g => Subtype.ext (C.Zs_central g.2 hd).symm, ?_⟩
        apply Subtype.ext
        show s * (C.zf ω * C.zf j) * s⁻¹ = C.zf ω * C.zf j * d
        rw [hde]
        exact (C.Zs_central hu hd).symm
      exact hG.sigma_eq_of_fix hz (conjHom K1 L2 S Zs hs) σ
        (fun i => ⟨c i, F112J2.Zs_le_vBeta K1 L2 S Zs (hcZ i)⟩)
        (fun i g => Subtype.ext (C.Zs_central g.2 (hcZ i)).symm)
        (fun i => Subtype.ext (hcE i)) hωj hωk hjk (hpair j hj hωj) (hpair k hk hωk)
    rw [hσ ω, hσω]

omit [DecidableEq Ω] in
theorem comm_S_vBeta_mem_evenSub {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) {s : G} (hs : s ∈ S) {x : G}
    (hx : x ∈ vBeta K1 L2 S Zs) :
    ∃ y ∈ (C.gramRel hij).evenSub, (y : G) = s * x * s⁻¹ * x⁻¹ := by
  obtain ⟨σ, c, hcZ, hcE, -⟩ := C.exists_sigma hs
  have hG := C.gramRel hij
  have hclos : (⟨x, hx⟩ : ↥(vBeta K1 L2 S Zs)) ∈
      Subgroup.closure (insert (C.zU i₀ j₀) (Set.range C.wU)) := by
    rw [C.closure_wU hij]
    exact Subgroup.mem_top _
  choose e he using fun i => C.exists_pow_zU hij (hcZ i)
  have hφz : conjHom K1 L2 S Zs hs (C.zU i₀ j₀) = C.zU i₀ j₀ := by
    apply Subtype.ext
    show s * C.cm i₀ j₀ * s⁻¹ = C.cm i₀ j₀
    have := Subgroup.mem_centralizer_iff.mp (F112J2.S_le_centralizer_Z C.h hs) _
      (C.cm_mem i₀ j₀)
    rw [← this]
    group
  have hφ : ∀ i, conjHom K1 L2 S Zs hs (C.wU i) = C.wU (σ i) * (C.zU i₀ j₀) ^ (e i) := by
    intro i
    apply Subtype.ext
    show s * C.zf i * s⁻¹ = ((C.wU (σ i) * (C.zU i₀ j₀) ^ (e i) : ↥(vBeta K1 L2 S Zs)) : G)
    rw [Subgroup.coe_mul, Subgroup.coe_pow, hcE i, he i]
    rfl
  have := hG.hom_mul_inv_mem_evenSub (conjHom K1 L2 S Zs hs) hφz σ e hφ hclos
  exact ⟨_, this, rfl⟩

end Fix

end FamCtx

end SzR1

end CFSG.Quasithin
