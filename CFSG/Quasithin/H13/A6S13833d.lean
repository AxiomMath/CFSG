module

public import CFSG.Quasithin.H13.A6S13833c

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

@[expose] def FpfMoves (σ : Perm (Fin 6)) : Prop := FPF σ → act4f σ e0123 ≠ e0123

instance (σ : Perm (Fin 6)) : Decidable (FpfMoves σ) := by unfold FpfMoves; infer_instance

theorem fpfMoves_all : ∀ σ : Perm (Fin 6), FpfMoves σ := by decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem mem_normalizer_V3_of_le {x : G} (h : ∀ v ∈ S.V3, x * v * x⁻¹ ∈ S.V3) :
    x ∈ Subgroup.normalizer (S.V3 : Set G) := by
  have h1 : conjSub x S.V3 ≤ S.V3 := fun y hy => by
    have := h _ (mem_conjSub.mp hy)
    simpa [mul_assoc] using this
  have e : conjSub x S.V3 = S.V3 := Subgroup.eq_of_le_of_card_ge h1
    (by rw [CosetGeom.card_conjSub])
  refine F7.mem_normalizer_of_conj_le e.le ?_
  rw [← e, conjSub_conjSub_inv, e]

theorem exists_L2_not_NV3 (h13315 : Stmt13_3_15) (hhat : ¬ IsHatA6 L) :
    ∃ x ∈ S.L2, (∃ m : ℕ, Odd m ∧ x ^ m = 1) ∧ ∃ v ∈ S.V3, x * v * x⁻¹ ∉ S.V3 := by
  obtain ⟨x, hxX, ⟨m, hm, hxm⟩, hxC, hxN⟩ := S.exists_X2_elem h13315
  rw [S.X2_not_hat hhat] at hxX
  refine ⟨x, hxX, ⟨m, hm, hxm⟩, ?_⟩
  by_contra hall
  push Not at hall
  have hxL : x ∈ L := S.L2_le_L hxX
  set xN : ↥(Subgroup.normalizer (V : Set G)) := ⟨x, S.frame.L_le hxL⟩ with hxNdef
  have hx' : xN ^ m = 1 := Subtype.ext (by simpa using hxm)
  have h45 : (S.frame.ρ xN) ^ 45 = 1 := by
    refine pow_45_of_odd hm ?_
    rw [← map_pow, hx', map_one]
  obtain ⟨hfpf, -⟩ := fpf_of _ (S.stabW2_of_mem (x := xN) hxN) h45
    (S.movesW2_of_not_mem (x := xN) hxC)
  have hst : ∀ y : P6, InW4 y → InW3 y → InW3 (act4f (S.frame.ρ xN) y) := by
    intro y hy4 hy3
    obtain ⟨v, hv⟩ := S.frame.ψ.surjective ⟨y, hy4⟩
    have hv3 : (v : G) ∈ S.V3 := S.mem_pre.2 ⟨v.2, by
      have e : S.frame.ψ ⟨(v : G), v.2⟩ = ⟨y, hy4⟩ := hv
      rw [e]; exact hy3⟩
    obtain ⟨_, hW⟩ := S.mem_pre.1 (hall v hv3)
    have e : S.frame.ψ ⟨x * v * x⁻¹, (Subgroup.mem_normalizer_iff.mp xN.2 v).mp v.2⟩ =
        act4 (S.frame.ρ xN) ⟨y, hy4⟩ := by
      rw [S.psi_conj xN v, hv]
    have hW' : S.frame.ψ ⟨x * v * x⁻¹, (Subgroup.mem_normalizer_iff.mp xN.2 v).mp v.2⟩ ∈
        W3sub := hW
    rw [e] at hW'
    exact hW'
  exact fpfMoves_all _ hfpf (stabW3e_all _ hst)

theorem V_eq_sup_of_not {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G)) {v : G}
    (hv : v ∈ S.V3) (hxv : x * v * x⁻¹ ∉ S.V3) : V = S.V3 ⊔ conjSub x S.V3 := by
  have hle : S.V3 ⊔ conjSub x S.V3 ≤ V := by
    refine sup_le S.V3_le_V fun y hy => ?_
    have h1 : x⁻¹ * y * x ∈ V := S.V3_le_V (mem_conjSub.mp hy)
    have := (Subgroup.mem_normalizer_iff.mp hxV _).mp h1
    simpa [mul_assoc] using this
  refine le_antisymm (fun y hy => ?_) hle
  have hw : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV v).mp (S.V3_le_V hv)
  by_cases hy3 : y ∈ S.V3
  · exact Subgroup.mem_sup_left hy3
  · have h1 := inv_mul_mem_of_relIndex_two S.relIndex_V3_V hw hy hxv hy3
    have e : y = (x * v * x⁻¹) * ((x * v * x⁻¹)⁻¹ * y) := by group
    rw [e]
    exact (S.V3 ⊔ conjSub x S.V3).mul_mem (Subgroup.mem_sup_right (mul_mem_conjSub hv))
      (Subgroup.mem_sup_left h1)

theorem normalizes_V2_of {k : G} (hk : k ∈ S.G1) (hku : S.u1⁻¹ * (k * S.u1 * k⁻¹) ∈ fsuV1 T V) :
    k ∈ Subgroup.normalizer (S.V2 : Set G) := by
  have hkz : k * S.z * k⁻¹ = S.z := by
    have h : k * S.z = S.z * k := Subgroup.mem_centralizer_singleton_iff.mp hk
    rw [h, mul_inv_cancel_right]
  have hV1 : ∀ y ∈ fsuV1 T V, k * y * k⁻¹ ∈ fsuV1 T V := by
    intro y hy
    rcases (S.mem_V1_iff).1 hy with rfl | rfl
    · simp
    · rw [hkz]; exact hy
  have h12 : (fsuV1 T V).relIndex S.V2 = 2 := by
    have h1 := Subgroup.relIndex_mul_card (fsuV1 T V) S.V2
    rw [inf_eq_left.2 S.V1_le_V2, S.card_V2, S.card_V1] at h1
    omega
  have hle : ∀ y ∈ S.V2, k * y * k⁻¹ ∈ S.V2 := by
    intro y hy
    by_cases hy1 : y ∈ fsuV1 T V
    · exact S.V1_le_V2 (hV1 y hy1)
    · have h1 := inv_mul_mem_of_relIndex_two h12 S.u1_mem_V2 hy S.u1_not_V1 hy1
      have e : k * y * k⁻¹ = (k * S.u1 * k⁻¹) * (k * (S.u1⁻¹ * y) * k⁻¹) := by group
      rw [e]
      refine S.V2.mul_mem ?_ (S.V1_le_V2 (hV1 _ h1))
      have e2 : k * S.u1 * k⁻¹ = S.u1 * (S.u1⁻¹ * (k * S.u1 * k⁻¹)) := by group
      rw [e2]
      exact S.V2.mul_mem S.u1_mem_V2 (S.V1_le_V2 hku)
  have h1 : conjSub k S.V2 ≤ S.V2 := fun y hy => by
    have := hle _ (mem_conjSub.mp hy)
    simpa [mul_assoc] using this
  have e : conjSub k S.V2 = S.V2 := Subgroup.eq_of_le_of_card_ge h1
    (by rw [CosetGeom.card_conjSub])
  refine F7.mem_normalizer_of_conj_le e.le ?_
  rw [← e, conjSub_conjSub_inv, e]

variable (h13315 : Stmt13_3_15) (hhat : ¬ IsHatA6 L)
include h13315 hhat

theorem normalizer_V2_le_normalizer_L2 :
    Subgroup.normalizer (S.V2 : Set G) ≤ Subgroup.normalizer (S.L2 : Set G) := by
  have h := S.NV2_le_NX2 h13315
  rwa [S.X2_not_hat hhat] at h

theorem U2_le_UL : S.U2 ≤ conjClosure (conjClosure S.V3 S.G1) L := by
  obtain ⟨x, hxL2, -, v, hv, hxv⟩ := S.exists_L2_not_NV3 h13315 hhat
  have hxL : x ∈ L := S.L2_le_L hxL2
  have hV := S.V_eq_sup_of_not (S.frame.L_le hxL) hv hxv
  refine conjClosure_le fun k hk y hy => ?_
  have hkH := S.K2_le_G1 hk
  have hkL2 : k ∈ Subgroup.normalizer (S.L2 : Set G) :=
    S.normalizer_V2_le_normalizer_L2 h13315 hhat (S.K2_le_normalizer_V2 hk)
  rw [hV] at hy
  have hy' : k * y * k⁻¹ ∈ conjSub k (S.V3 ⊔ conjSub x S.V3) := mul_mem_conjSub hy
  rw [conjSub, Subgroup.map_sup] at hy'
  refine (sup_le (a := conjSub k S.V3) ?_ ?_) hy'
  · intro w hw
    have hw' : w ∈ conjSub k S.V3 := hw
    have := (HypF91.conjSub_le_conjClosure (Z := S.V3) hkH) hw'
    exact le_conjClosure _ L this
  · intro w hw
    have hw' : w ∈ conjSub k (conjSub x S.V3) := hw
    rw [← conjSub_mul] at hw'
    have e : k * x = (k * x * k⁻¹) * k := by group
    rw [e, conjSub_mul] at hw'
    have hkx : k * x * k⁻¹ ∈ L := S.L2_le_L ((Subgroup.mem_normalizer_iff.mp hkL2 x).mp hxL2)
    have h1 : conjSub k S.V3 ≤ conjClosure S.V3 S.G1 := HypF91.conjSub_le_conjClosure hkH
    exact (HypF91.conjSub_le_conjClosure (Z := conjClosure S.V3 S.G1) hkx) (conjSub_mono _ h1 hw')

omit h13315 hhat in
theorem U2_le_sup {x : G} (hxL2 : x ∈ S.L2) {v : G} (hv : v ∈ S.V3) (hxv : x * v * x⁻¹ ∉ S.V3) :
    S.U2 ≤ S.U21 ⊔ conjSub x S.U21 := by
  have hxL : x ∈ L := S.L2_le_L hxL2
  have hV := S.V_eq_sup_of_not (S.frame.L_le hxL) hv hxv
  have hxK : x⁻¹ ∈ Subgroup.normalizer (S.K2 : Set G) :=
    S.normalizer_V2_le_normalizer_K2 (S.L2_le_NV2 (S.L2.inv_mem hxL2))
  refine conjClosure_le fun k hk y hy => ?_
  rw [hV] at hy
  have hy' : k * y * k⁻¹ ∈ conjSub k (S.V3 ⊔ conjSub x S.V3) := mul_mem_conjSub hy
  rw [conjSub, Subgroup.map_sup] at hy'
  refine (sup_le (a := conjSub k S.V3) ?_ ?_) hy'
  · intro w hw
    exact Subgroup.mem_sup_left ((HypF91.conjSub_le_conjClosure (Z := S.V3) hk) hw)
  · intro w hw
    have hw' : w ∈ conjSub k (conjSub x S.V3) := hw
    rw [← conjSub_mul] at hw'
    have e : k * x = x * (x⁻¹ * k * x) := by group
    rw [e, conjSub_mul] at hw'
    have hk' : x⁻¹ * k * x ∈ S.K2 := by
      have := (Subgroup.mem_normalizer_iff.mp hxK k).mp hk
      simpa using this
    exact Subgroup.mem_sup_right (conjSub_mono x (HypF91.conjSub_le_conjClosure hk') hw')


section NatU2

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (AltHeart 6)} (hβs : Function.Surjective β)
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
      (QuotientAddGroup.mk (permWeight 6 (ρ h) x) : AltHeart 6) = Multiplicative.toAdd (β v))
  {τ : Perm (Fin 6)} {ρ' : ↥S.G1 →* Perm (Fin 6)} (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
  (hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  {K : Subgroup G}
  (honto' : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ' k = σ)
include hβs hβk hβe hρ' hN' honto'

omit h13315 hhat hβs in
theorem exists_K2_not_NV3 : ∃ k ∈ S.K2, ∃ v ∈ S.V3, k * v * k⁻¹ ∉ S.V3 := by
  obtain ⟨r₂, hr₂, -⟩ :=
    exists_rep5 (Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩))
  set q := vp τ⁻¹ (r₂ : Fin 6 → ZMod 2) with hq
  have hql := S.nat_V3_line hβk hβe hρ' hN' honto' S.u1_mem_V3 r₂ hr₂
  have hq0 : ¬ (q = 0 ∨ q = onesV) := by
    intro h
    apply S.u1_not_V1
    refine (hβk ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩).1 (Multiplicative.toAdd.injective ?_)
    rw [toAdd_one, ← hr₂]
    refine (mk_eq_zero_iff r₂).2 ?_
    rcases h with h | h
    · left; exact vp_injective τ⁻¹ (by rw [← hq, h, vp_zero])
    · right; exact vp_injective τ⁻¹ (by rw [← hq, h]; exact (vp_const τ⁻¹).symm)
  obtain ⟨σ, hσ, hσq, hσι⟩ := outAt_all q hql hq0
  obtain ⟨hs, h3, -⟩ := c3Out_facts σ hσ
  obtain ⟨k₀, -, hk₀⟩ := honto' σ (Perm.mem_alternatingGroup.mpr hs)
  have hk₀u : S.u1⁻¹ * ((k₀ : G) * S.u1 * (k₀ : G)⁻¹) ∈ fsuV1 T V := by
    have hUN := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 k₀.2)
      S.u1).mp (S.V3_le_UH S.u1_mem_V3)
    have he := hβe k₀ ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩ ⟨_, hUN⟩ rfl r₂ hr₂
    have hb : β ⟨_, hUN⟩ = β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩ := by
      apply Multiplicative.toAdd.injective
      rw [← he, ← hr₂, mk_eq_mk_iff]
      have e : vp τ⁻¹ ((permWeight 6 (ρ k₀) r₂ : ↥(evenWeight 6)) : Fin 6 → ZMod 2) =
          vp σ q := by
        show vp τ⁻¹ (vp (ρ k₀) (r₂ : Fin 6 → ZMod 2)) = _
        rw [← hk₀, hq, hρ', ← vp_mul, ← vp_mul]; congr 1; group
      rcases hσq with h | h
      · left
        apply vp_injective τ⁻¹
        rw [e, h]
      · right
        apply vp_injective τ⁻¹
        rw [e, h, vp_add, vp_const]
    have := (hβk ((⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩ : ↥(conjClosure S.V3 S.G1))⁻¹ *
      ⟨_, hUN⟩)).1 (by rw [map_mul, map_inv, hb, inv_mul_cancel])
    exact this
  have hk₀N := S.normalizes_V2_of k₀.2 hk₀u
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (k₀ : G)).ne'
  set k₁ : G := (k₀ : G) ^ (2 ^ a) with hk₁
  have hk₁m : k₁ ^ m = 1 := by rw [hk₁, ← pow_mul, ← hnm, pow_orderOf_eq_one]
  have hk₁H : k₁ ∈ S.G1 := S.G1.pow_mem k₀.2 _
  have hk₁N : k₁ ∈ Subgroup.normalizer (S.V2 : Set G) := Subgroup.pow_mem _ hk₀N _
  have hk₁C : k₁ ∈ Subgroup.centralizer (S.V2 : Set G) := by
    have hkz : k₁ * S.z * k₁⁻¹ = S.z := by
      have h : k₁ * S.z = S.z * k₁ := Subgroup.mem_centralizer_singleton_iff.mp hk₁H
      rw [h, mul_inv_cancel_right]
    have hz2 : S.z * S.z = 1 := by
      have := isElemAbelian_pow_eq_one S.elemAbelian_V S.z_mem_V
      rwa [pow_two] at this
    have hV1 : ∀ y ∈ fsuV1 T V, k₁ * y * k₁⁻¹ = y := by
      intro y hy
      rcases (S.mem_V1_iff).1 hy with rfl | rfl
      · group
      · exact hkz
    have h12 : (fsuV1 T V).relIndex S.V2 = 2 := by
      have h1 := Subgroup.relIndex_mul_card (fsuV1 T V) S.V2
      rw [inf_eq_left.2 S.V1_le_V2, S.card_V2, S.card_V1] at h1
      omega
    have hku : S.u1⁻¹ * (k₁ * S.u1 * k₁⁻¹) ∈ fsuV1 T V := by
      have hmem : k₁ * S.u1 * k₁⁻¹ ∈ S.V2 :=
        (Subgroup.mem_normalizer_iff.mp hk₁N S.u1).mp S.u1_mem_V2
      by_contra hne
      have hnot : k₁ * S.u1 * k₁⁻¹ ∉ fsuV1 T V := by
        intro h
        apply S.u1_not_V1
        have := (Subgroup.mem_normalizer_iff.mp
          (S.normalizer_V1 ▸ (hk₁H : k₁ ∈ Subgroup.centralizer ({S.z} : Set G)) :
            k₁ ∈ Subgroup.normalizer (fsuV1 T V : Set G)) _).mpr h
        exact this
      exact hne (inv_mul_mem_of_relIndex_two h12 S.u1_mem_V2 hmem S.u1_not_V1 hnot)
    have hu : k₁ * S.u1 * k₁⁻¹ = S.u1 := by
      rcases (S.mem_V1_iff).1 hku with h | h
      · calc k₁ * S.u1 * k₁⁻¹ = S.u1 * (S.u1⁻¹ * (k₁ * S.u1 * k₁⁻¹)) := by group
          _ = S.u1 := by rw [h, mul_one]
      · exfalso
        have hs : k₁ * S.u1 * k₁⁻¹ = S.u1 * S.z := by
          calc k₁ * S.u1 * k₁⁻¹ = S.u1 * (S.u1⁻¹ * (k₁ * S.u1 * k₁⁻¹)) := by group
            _ = S.u1 * S.z := by rw [h]
        have hj : ∀ j : ℕ, k₁ ^ j * S.u1 * (k₁ ^ j)⁻¹ = S.u1 * S.z ^ j := by
          intro j
          induction j with
          | zero => simp
          | succ j ih =>
            calc k₁ ^ (j + 1) * S.u1 * (k₁ ^ (j + 1))⁻¹ =
                k₁ * (k₁ ^ j * S.u1 * (k₁ ^ j)⁻¹) * k₁⁻¹ := by group
              _ = (k₁ * S.u1 * k₁⁻¹) * (k₁ * S.z ^ j * k₁⁻¹) := by rw [ih]; group
              _ = S.u1 * S.z * S.z ^ j := by rw [hs, ← conj_pow, hkz]
              _ = S.u1 * S.z ^ (j + 1) := by rw [pow_succ']; group
        have hm2 := hj m
        rw [hk₁m, one_mul, inv_one, mul_one] at hm2
        obtain ⟨j, rfl⟩ := hm
        rw [pow_succ, pow_mul, pow_two, hz2, one_pow, one_mul] at hm2
        exact S.z_ne_one (by
          have := congrArg (S.u1⁻¹ * ·) hm2
          simpa using this.symm)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    by_cases hy1 : y ∈ fsuV1 T V
    · have := hV1 y hy1
      calc y * k₁ = (k₁ * y * k₁⁻¹) * k₁ := by rw [this]
        _ = k₁ * y := by group
    · have h1 := inv_mul_mem_of_relIndex_two h12 S.u1_mem_V2 hy S.u1_not_V1 hy1
      have hw := hV1 _ h1
      have e : k₁ * y * k₁⁻¹ = y := by
        calc k₁ * y * k₁⁻¹ = (k₁ * S.u1 * k₁⁻¹) * (k₁ * (S.u1⁻¹ * y) * k₁⁻¹) := by group
          _ = y := by rw [hu, hw]; group
      calc y * k₁ = (k₁ * y * k₁⁻¹) * k₁ := by rw [e]
        _ = k₁ * y := by group
  have hk₁K : k₁ ∈ S.K2 := Subgroup.subset_closure ⟨hk₁C, m, hm, hk₁m⟩
  refine ⟨k₁, hk₁K, ?_⟩
  by_contra hall
  push Not at hall
  have hk₁3 := S.mem_normalizer_V3_of_le hall
  have hc := (hN' ⟨k₁, hk₁H⟩).2 hk₁3
  have hcomm := cList_comm _ hc
  have e : ρ' ⟨k₁, hk₁H⟩ = σ ^ (2 ^ a) := by
    rw [← hk₀, ← map_pow]; rfl
  rw [e] at hcomm
  apply hσι
  have h4 : σ = (σ ^ (2 ^ a)) ^ (2 ^ a) := by
    rw [← pow_mul, show (2 : ℕ) ^ a * 2 ^ a = 4 ^ a by rw [← mul_pow]; norm_num]
    exact (pow_four_pow_of_cube h3 a).symm
  rw [h4]
  exact (Commute.pow_left hcomm _).eq

end NatU2


section NatU2Card

variable (hNS : ¬ LieModel G .PSp 3 2 1)
  (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz) (h13314 : Stmt13_3_14)
  (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
  {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (AltHeart 6)} (hβs : Function.Surjective β)
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
      (QuotientAddGroup.mk (permWeight 6 (ρ h) x) : AltHeart 6) = Multiplicative.toAdd (β v))
  {τ : Perm (Fin 6)} {ρ' : ↥S.G1 →* Perm (Fin 6)} (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
  (hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  (hker' : ∀ h : ↥S.G1, ρ' h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
  {K : Subgroup G} (hKT : K ⊔ T = S.G1)
  (hKA' : ∀ k : ↥S.G1, (k : G) ∈ K → ρ' k ∈ alternatingGroup (Fin 6))
  (honto' : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ' k = σ)
include hNS h1356two hG1 h13314 hF hβs hβk hβe hρ' hN' hker' hKT hKA' honto'

omit h13315 hhat hNS h1356two hG1 h13314 hF hβs hβk hβe hρ' hN'
  hker' hKT hKA' honto' in
theorem sign_K2 {k : G} (hk : k ∈ S.K2) : Perm.sign (ρ' ⟨k, S.K2_le_G1 hk⟩) = 1 := by
  have key : ∀ y ∈ S.K2, ∀ hy : y ∈ S.G1, Perm.sign (ρ' ⟨y, hy⟩) = 1 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      intro hxH
      obtain ⟨-, m, hm, hxm⟩ := hx
      have h1 : (ρ' ⟨x, hxH⟩) ^ m = 1 := by
        rw [← map_pow]
        have : (⟨x, hxH⟩ : ↥S.G1) ^ m = 1 := Subtype.ext (by simpa using hxm)
        rw [this, map_one]
      have h2 : (Perm.sign (ρ' ⟨x, hxH⟩)) ^ m = 1 := by rw [← map_pow, h1, map_one]
      rcases Int.units_eq_one_or (Perm.sign (ρ' ⟨x, hxH⟩)) with h | h
      · exact h
      · rw [h, hm.neg_one_pow] at h2
        exact absurd h2 (by decide)
    | one =>
      intro h
      have e : (⟨1, h⟩ : ↥S.G1) = 1 := rfl
      rw [e, map_one, map_one]
    | mul x y _ _ ihx ihy =>
      intro hxy
      have hx' : x ∈ S.G1 := S.K2_le_G1 ‹_›
      have hy' : y ∈ S.G1 := S.K2_le_G1 ‹_›
      have e : (⟨x * y, hxy⟩ : ↥S.G1) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := rfl
      rw [e, map_mul, map_mul, ihx hx', ihy hy', one_mul]
    | inv x _ ihx =>
      intro hx
      have hx' : x ∈ S.G1 := by simpa using S.G1.inv_mem hx
      have e : (⟨x⁻¹, hx⟩ : ↥S.G1) = (⟨x, hx'⟩)⁻¹ := rfl
      rw [e, map_inv, map_inv, ihx hx', inv_one]
  exact key k hk _

omit h13315 hhat hNS h1356two hG1 h13314 hF hker' hKT hKA' in
theorem card_U21_nat : Nat.card S.U21 = 16 := by
  have hle := S.card_U21_le_nat hβs hβk hβe hρ' hN' honto'
  obtain ⟨k, hk, v, hv, hkv⟩ := S.exists_K2_not_NV3 hβk hβe hρ' hN' honto'
  have hlt : S.V3 < S.U21 := lt_of_le_of_ne S.V3_le_U21 fun h =>
    hkv (h ▸ (HypF91.conjSub_le_conjClosure (Z := S.V3) hk) (mul_mem_conjSub hv))
  have hd : Nat.card S.V3 ∣ Nat.card S.U21 := Subgroup.card_dvd_of_le hlt.le
  have hne : Nat.card S.V3 ≠ Nat.card S.U21 := fun h =>
    hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le h.ge)
  rw [S.card_V3] at hd hne
  obtain ⟨c, hc⟩ := hd
  have hpos : 0 < Nat.card S.U21 := Nat.card_pos
  rw [hc] at hle hne hpos ⊢
  have : c = 2 := by omega
  rw [this]

omit hNS h1356two hG1 h13314 hF hker' hKT hKA' in
theorem card_U2_le_nat (hab : IsMulCommutative ↥(conjClosure V S.G1)) : Nat.card S.U2 ≤ 64 := by
  obtain ⟨x, hxL2, -, v, hv, hxv⟩ := S.exists_L2_not_NV3 h13315 hhat
  have hU := S.U2_le_sup hxL2 hv hxv
  have hxN : x ∈ Subgroup.normalizer (S.U2 : Set G) :=
    S.normalizes_U2 (S.L2_le_NV2 hxL2) (S.frame.L_le (S.L2_le_L hxL2))
  have hxU : conjSub x S.U21 ≤ S.U2 := fun y hy => by
    have h1 := S.U21_le_U2 (mem_conjSub.mp hy)
    have := (Subgroup.mem_normalizer_iff.mp hxN _).mp h1
    simpa [mul_assoc] using this
  have hcomm : S.U21 ≤ Subgroup.normalizer (conjSub x S.U21 : Set G) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 := S.U2_le_VH (S.U21_le_U2 ha)
    have h2 := S.U2_le_VH (hxU hb)
    have := mul_comm' (⟨b, h2⟩ : ↥(conjClosure V S.G1)) ⟨a, h1⟩
    exact congrArg Subtype.val this
  have hprod := card_sup_mul_card_inf' hcomm
  have hV2 : S.V2 ≤ S.U21 ⊓ conjSub x S.U21 := by
    refine le_inf (S.V2_le_V3.trans S.V3_le_U21) ?_
    have e : conjSub x S.V2 = S.V2 :=
      F7.conjSub_eq_of_mem_normalizer (S.L2_le_NV2 hxL2)
    rw [← e]
    exact conjSub_mono x (S.V2_le_V3.trans S.V3_le_U21)
  have h4 : 4 ≤ Nat.card ↥(S.U21 ⊓ conjSub x S.U21) := by
    rw [← S.card_V2]; exact Subgroup.card_le_of_le hV2
  have h16 := S.card_U21_nat hβs hβk hβe hρ' hN' honto'
  rw [h16, CosetGeom.card_conjSub, h16] at hprod
  have hsup : Nat.card ↥(S.U21 ⊔ conjSub x S.U21) ≤ 64 := by nlinarith
  exact (Subgroup.card_le_of_le hU).trans hsup

theorem card_U2_nat : Nat.card S.U2 = 64 := by
  set U := conjClosure S.V3 S.G1 with hUdef
  have hab : IsMulCommutative ↥(conjClosure V S.G1) := hF.F911_2.1
  have hle := S.card_U2_le_nat h13315 hhat hβs hβk hβe hρ' hN' honto' hab
  have h16 := S.card_U21_nat hβs hβk hβe hρ' hN' honto'
  have hTH : T ≤ S.G1 := hKT ▸ le_sup_right
  have hUN : ∀ h ∈ S.G1, ∀ u ∈ U, h * u * h⁻¹ ∈ U := fun h hh u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hh) u).mp hu
  have hVU : V ≤ Subgroup.normalizer (U : Set G) := fun v hv =>
    le_normalizer_conjClosure S.V3 S.G1 (hF.toHypF91.V_le_H hv)
  have hVinf : V ⊓ U = S.V3 := S.V_inf_UH hNS h13315 h1356two hG1 h13314
  have hVU21 : V ≤ Subgroup.normalizer (S.U21 : Set G) := fun v hv =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb => by
      have h1 := S.U2_le_VH (S.U21_le_U2 hb)
      have h2 := le_conjClosure V S.G1 hv
      exact congrArg Subtype.val (mul_comm' (⟨b, h1⟩ : ↥(conjClosure V S.G1)) ⟨v, h2⟩))
  have hinf21 : V ⊓ S.U21 = S.V3 := le_antisymm
    (fun y hy => hVinf ▸ ⟨hy.1, S.U21_le_UH hy.2⟩) (le_inf S.V3_le_V S.V3_le_U21)
  have hc1 := card_sup_mul_card_inf' hVU21
  rw [hinf21, S.card_V, h16, S.card_V3] at hc1
  have hcVU21 : Nat.card ↥(V ⊔ S.U21) = 32 := by omega
  have hsub : V ⊔ S.U21 ≤ S.U2 := sup_le S.V_le_U2 S.U21_le_U2
  have hd : Nat.card ↥(V ⊔ S.U21) ∣ Nat.card S.U2 := Subgroup.card_dvd_of_le hsub
  rw [hcVU21] at hd
  obtain ⟨c, hc⟩ := hd
  have hpos : 0 < Nat.card S.U2 := Nat.card_pos
  rw [hc] at hle hpos ⊢
  have hc12 : c = 1 ∨ c = 2 := by omega
  rcases hc12 with rfl | rfl
  swap
  · rfl
  exfalso
  have heq : S.U2 = V ⊔ S.U21 := (Subgroup.eq_of_le_of_card_ge hsub (by rw [hc, hcVU21])).symm
  have hKN : ∀ k ∈ S.K2, k ∈ Subgroup.normalizer ((V ⊔ U : Subgroup G) : Set G) := by
    intro k hk
    have hkH := S.K2_le_G1 hk
    have h1 : conjSub k (V ⊔ U) ≤ V ⊔ U := by
      rw [conjSub, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · intro y hy
        have hy' : y ∈ conjSub k V := hy
        have := (HypF91.conjSub_le_conjClosure (Z := V) hk) hy'
        rw [show conjClosure V S.K2 = S.U2 from rfl, heq] at this
        exact (sup_le le_sup_left (S.U21_le_UH.trans le_sup_right)) this
      · intro y hy
        have hy' : y ∈ conjSub k U := hy
        rw [F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure S.V3 S.G1 hkH)] at hy'
        exact Subgroup.mem_sup_right hy'
    have e : conjSub k (V ⊔ U) = V ⊔ U :=
      Subgroup.eq_of_le_of_card_ge h1 (by rw [CosetGeom.card_conjSub])
    refine F7.mem_normalizer_of_conj_le e.le ?_
    rw [← e, conjSub_conjSub_inv, e]
  have hN3 : ∀ h ∈ S.G1, h ∈ Subgroup.normalizer (S.V3 : Set G) →
      h ∈ Subgroup.normalizer ((V ⊔ U : Subgroup G) : Set G) := by
    intro h hh h3
    have hV := S.G1_inf_G3_le h13315 ⟨hh, h3⟩
    have e : conjSub h (V ⊔ U) = V ⊔ U := by
      rw [conjSub, Subgroup.map_sup]
      change conjSub h V ⊔ conjSub h U = V ⊔ U
      rw [F7.conjSub_eq_of_mem_normalizer hV,
        F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure S.V3 S.G1 hh)]
    refine F7.mem_normalizer_of_conj_le e.le ?_
    rw [← e, conjSub_conjSub_inv, e]
  set N : Subgroup G := S.G1 ⊓ Subgroup.normalizer ((V ⊔ U : Subgroup G) : Set G) with hNdef
  set X : Subgroup (Perm (Fin 6)) := (N.subgroupOf S.G1).map ρ' with hXdef
  have hCX : cA6 ≤ X := by
    intro σ hσ
    obtain ⟨k, -, hk⟩ := honto' σ (Perm.mem_alternatingGroup.mpr hσ.2)
    have hk3 : (k : G) ∈ Subgroup.normalizer (S.V3 : Set G) :=
      (hN' k).1 (by rw [hk]; exact mem_cList σ hσ.1)
    exact ⟨k, Subgroup.mem_subgroupOf.mpr ⟨k.2, hN3 _ k.2 hk3⟩, hk⟩
  obtain ⟨k, hk, v, hv, hkv⟩ := S.exists_K2_not_NV3 hβk hβe hρ' hN' honto'
  have hkH := S.K2_le_G1 hk
  have hsX : ρ' ⟨k, hkH⟩ ∈ X :=
    ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr ⟨hkH, hKN k hk⟩, rfl⟩
  have hsι : ρ' ⟨k, hkH⟩ * iota0 ≠ iota0 * ρ' ⟨k, hkH⟩ := by
    intro h
    apply hkv
    have := (hN' ⟨k, hkH⟩).1 (mem_cList _ h)
    exact (Subgroup.mem_normalizer_iff.mp this v).mp hv
  have hAX := alt6_le_of_overgroup hCX hsX (S.sign_K2 hk) hsι
  have hQN : pCoreOf 2 S.G1 ≤ N := by
    intro q hq
    refine ⟨pCoreOf_le 2 S.G1 hq, ?_⟩
    have hqN : q ∈ Subgroup.normalizer (V : Set G) :=
      (S.rho_QH_mem_R8 hNS h13315 h1356two hG1 hq).1
    have e : conjSub q (V ⊔ U) = V ⊔ U := by
      rw [conjSub, Subgroup.map_sup]
      change conjSub q V ⊔ conjSub q U = V ⊔ U
      rw [F7.conjSub_eq_of_mem_normalizer hqN, F7.conjSub_eq_of_mem_normalizer
        (le_normalizer_conjClosure S.V3 S.G1 (pCoreOf_le 2 S.G1 hq))]
    refine F7.mem_normalizer_of_conj_le e.le ?_
    rw [← e, conjSub_conjSub_inv, e]
  have hHN : S.G1 ≤ N := by
    rw [← hKT]
    refine sup_le (fun y hy => ?_) (fun t ht => ⟨hTH ht, hN3 t (hTH ht)
      (S.T_le_normalizer_V3 ht)⟩)
    have hyH : y ∈ S.G1 := hKT ▸ Subgroup.mem_sup_left hy
    obtain ⟨n, hn, hny⟩ := hAX (hKA' ⟨y, hyH⟩ hy)
    have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
    have hq : ((n⁻¹ * ⟨y, hyH⟩ : ↥S.G1) : G) ∈ pCoreOf 2 S.G1 :=
      (hker' _).1 (by rw [map_mul, map_inv, hny, inv_mul_cancel])
    have e : y = (n : G) * ((n⁻¹ * ⟨y, hyH⟩ : ↥S.G1) : G) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]; group
    rw [e]
    exact N.mul_mem hnN (hQN hq)
  have hVH : conjClosure V S.G1 ≤ V ⊔ U := conjClosure_le fun h hh v hv => by
    have hN := (hHN hh).2
    exact (Subgroup.mem_normalizer_iff.mp hN v).mp (Subgroup.mem_sup_left hv)
  have hc2 := card_sup_mul_card_inf' hVU
  rw [hVinf, S.card_V, S.card_V3, S.card_UH_nat hβs hβk] at hc2
  have hcVU : Nat.card ↥(V ⊔ U) = 64 := by omega
  have hrel : U.relIndex (V ⊔ U) = 2 := by
    have h1 := Subgroup.relIndex_mul_card U (V ⊔ U)
    rw [inf_eq_left.2 le_sup_right, hcVU, S.card_UH_nat hβs hβk] at h1
    omega
  apply S.not_comm_VH_H_le_UH hNS h13315 h1356two hG1 h13314
  intro h hh x hx
  have hxU : x ∈ V ⊔ U := hVH hx
  have hhx : h * x * h⁻¹ ∈ V ⊔ U :=
    hVH ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V S.G1 hh) x).mp hx)
  by_cases hxu : x ∈ U
  · exact U.mul_mem (hUN h hh x hxu) (U.inv_mem hxu)
  · have hhxu : h * x * h⁻¹ ∉ U := fun h' => hxu (by
      have := hUN _ (S.G1.inv_mem hh) _ h'
      simpa [mul_assoc] using this)
    have h1 := inv_mul_mem_of_relIndex_two hrel hxU hhx hxu hhxu
    have hxH : x ∈ S.G1 := (conjClosure_le fun g hg v hv =>
      S.G1.mul_mem (S.G1.mul_mem hg (hF.toHypF91.V_le_H hv)) (S.G1.inv_mem hg)) hx
    have e : h * x * h⁻¹ * x⁻¹ = x * (x⁻¹ * (h * x * h⁻¹)) * x⁻¹ := by group
    rw [e]
    exact hUN x hxH _ h1

end NatU2Card

end Setting4

end CFSG.Quasithin.H13.A6

