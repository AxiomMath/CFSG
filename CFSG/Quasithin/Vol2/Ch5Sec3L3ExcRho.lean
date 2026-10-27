module

public import CFSG.Quasithin.Vol2.Ch5Sec3L3ExcVz
public import CFSG.Quasithin.Vol2.Ch5Sec3L3ExcOrth
import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.Vol2.Ch5Sec3L3ExcDelta

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.Open CFSG.QuasithinUnique CFSG.Fischer CFSG.OPlusFourTwo Matrix
  CFSG.LieType.BorelTits

namespace ExcNF

variable {G : Type} [Group G] {T S V₁ V₂ Z : Subgroup G} (N : ExcNF T S V₁ V₂ Z)

abbrev Gz : Subgroup G := Subgroup.centralizer ({N.Φ (1, 0, 0)} : Set G)

theorem add_eq_zero_iff_eq' (u w : Fin 4 → ZMod 2) : u + w = 0 ↔ u = w := by
  have h : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide
  constructor
  · intro huw
    funext i
    exact (h _ _).mp (congrFun huw i)
  · rintro rfl
    funext i
    exact (h _ _).mpr rfl

theorem δ_eq_iff {y y' : G} (hy : y ∈ N.Q) (hy' : y' ∈ N.Q) :
    N.δ y = N.δ y' ↔ y⁻¹ * y' ∈ Subgroup.zpowers (N.Φ (1, 0, 0)) := by
  rw [← N.δ_eq_zero_iff (N.Q.mul_mem (N.Q.inv_mem hy) hy'), N.δ_mul (N.Q.inv_mem hy) hy',
    N.δ_inv hy, add_eq_zero_iff_eq']

theorem zpowers_le_Q : Subgroup.zpowers (N.Φ (1, 0, 0)) ≤ N.Q := by
  intro g hg
  rcases N.mem_zpowers_iff.mp hg with rfl | rfl
  · exact N.Q.one_mem
  · exact N.Φ_mem_Q (by norm_num) (by norm_num)

theorem z_ne_one : N.Φ (1, 0, 0) ≠ 1 := by
  intro h
  rw [← N.Φ_zero] at h
  exact one_ne_zero (N.Φ_inj h).1

variable {N} (hQN : N.Gz ≤ Subgroup.normalizer (N.Q : Set G))
include hQN

theorem conj_mem_Q {g y : G} (hg : g ∈ N.Gz) (hy : y ∈ N.Q) : g * y * g⁻¹ ∈ N.Q :=
  (Subgroup.mem_normalizer_iff.mp (hQN hg) y).mp hy

theorem δ_conj_congr {g y y' : G} (hg : g ∈ N.Gz) (hy : y ∈ N.Q) (hy' : y' ∈ N.Q)
    (h : N.δ y = N.δ y') : N.δ (g * y * g⁻¹) = N.δ (g * y' * g⁻¹) := by
  have hgz : g * N.Φ (1, 0, 0) = N.Φ (1, 0, 0) * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [N.δ_eq_iff (conj_mem_Q hQN hg hy) (conj_mem_Q hQN hg hy')]
  have hc := (N.δ_eq_iff hy hy').mp h
  have e : (g * y * g⁻¹)⁻¹ * (g * y' * g⁻¹) = g * (y⁻¹ * y') * g⁻¹ := by group
  rw [e, conj_mem_zpowers hgz hc]
  exact hc

omit hQN in
@[expose] noncomputable def rhoFun (N : ExcNF T S V₁ V₂ Z) (g : G) (v : Fin 4 → ZMod 2) :
    Fin 4 → ZMod 2 :=
  N.δ (g * N.sec v * g⁻¹)

theorem rhoFun_δ {g y : G} (hg : g ∈ N.Gz) (hy : y ∈ N.Q) :
    N.rhoFun g (N.δ y) = N.δ (g * y * g⁻¹) :=
  δ_conj_congr hQN hg (N.sec_mem _) hy (N.δ_sec _)

theorem rhoFun_add {g : G} (hg : g ∈ N.Gz) (v w : Fin 4 → ZMod 2) :
    N.rhoFun g (v + w) = N.rhoFun g v + N.rhoFun g w := by
  have h1 : N.δ (N.sec v * N.sec w) = v + w := by
    rw [N.δ_mul (N.sec_mem v) (N.sec_mem w), N.δ_sec, N.δ_sec]
  rw [← h1, rhoFun_δ hQN hg (N.Q.mul_mem (N.sec_mem v) (N.sec_mem w))]
  have e : g * (N.sec v * N.sec w) * g⁻¹ = (g * N.sec v * g⁻¹) * (g * N.sec w * g⁻¹) := by
    group
  rw [e, N.δ_mul (conj_mem_Q hQN hg (N.sec_mem v)) (conj_mem_Q hQN hg (N.sec_mem w))]
  rfl

theorem rhoFun_mul {g h : G} (hg : g ∈ N.Gz) (hh : h ∈ N.Gz) (v : Fin 4 → ZMod 2) :
    N.rhoFun (g * h) v = N.rhoFun g (N.rhoFun h v) := by
  show N.δ (g * h * N.sec v * (g * h)⁻¹) = N.rhoFun g (N.δ (h * N.sec v * h⁻¹))
  rw [rhoFun_δ hQN hg (conj_mem_Q hQN hh (N.sec_mem v))]
  congr 1
  group

omit hQN in
theorem rhoFun_one (v : Fin 4 → ZMod 2) : N.rhoFun 1 v = v := by
  show N.δ (1 * N.sec v * 1⁻¹) = v
  rw [one_mul, inv_one, mul_one, N.δ_sec]

theorem rhoFun_q0 {g : G} (hg : g ∈ N.Gz) (v : Fin 4 → ZMod 2) :
    q0 (N.rhoFun g v) = q0 v := by
  have hgz : g * N.Φ (1, 0, 0) = N.Φ (1, 0, 0) * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  set y := N.sec v with hy
  have hyQ : y ∈ N.Q := N.sec_mem v
  have hy' : g * y * g⁻¹ ∈ N.Q := conj_mem_Q hQN hg hyQ
  have e1 := N.mul_self_eq hy'
  have e2 := N.mul_self_eq hyQ
  have hyy : y * y ∈ Subgroup.zpowers (N.Φ (1, 0, 0)) := by
    rw [e2]
    split_ifs
    · exact Subgroup.mem_zpowers _
    · exact Subgroup.one_mem _
  have e3 : g * y * g⁻¹ * (g * y * g⁻¹) = y * y := by
    have e : g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
    rw [e, conj_mem_zpowers hgz hyy]
  rw [e3, e2] at e1
  have hδ : N.δ y = v := N.δ_sec v
  rw [hδ] at e1
  show q0 (N.δ (g * y * g⁻¹)) = q0 v
  have hz1 := N.z_ne_one
  have key : ∀ (p q : Prop) [Decidable p] [Decidable q],
      ((if p then N.Φ (1, 0, 0) else 1) = (if q then N.Φ (1, 0, 0) else 1)) → (p ↔ q) := by
    intro p q _ _ h
    by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, ↓reduceIte] at h
    · exact iff_of_true hp hq
    · exact absurd h hz1
    · exact absurd h.symm hz1
    · exact iff_of_false hp hq
  have h01 : ∀ a b : ZMod 2, (a = 1 ↔ b = 1) → a = b := by decide
  exact h01 _ _ (key _ _ e1).symm

@[expose] noncomputable def rhoLin (g : N.Gz) : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) where
  toFun := N.rhoFun g
  map_add' := rhoFun_add hQN g.2
  map_smul' c v := by
    have h0 : N.rhoFun g 0 = 0 := by
      have h := rhoFun_add hQN g.2 0 0
      rw [add_zero] at h
      exact left_eq_add.mp h
    have hc : ∀ k : ZMod 2, k = 0 ∨ k = 1 := by decide
    rcases hc c with rfl | rfl
    · simp only [zero_smul, RingHom.id_apply, h0]
    · simp only [one_smul, RingHom.id_apply]

theorem rhoLin_mul (g h : N.Gz) : rhoLin hQN (g * h) = (rhoLin hQN g).comp (rhoLin hQN h) :=
  LinearMap.ext fun v => rhoFun_mul hQN g.2 h.2 v

theorem rhoLin_one : rhoLin hQN 1 = LinearMap.id :=
  LinearMap.ext fun v => rhoFun_one (N := N) v

@[expose] noncomputable def rho : N.Gz →* (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ where
  toFun g :=
    { val := LinearMap.toMatrix' (rhoLin hQN g)
      inv := LinearMap.toMatrix' (rhoLin hQN g⁻¹)
      val_inv := by
        rw [← LinearMap.toMatrix'_comp, ← rhoLin_mul, mul_inv_cancel, rhoLin_one,
          LinearMap.toMatrix'_id]
      inv_val := by
        rw [← LinearMap.toMatrix'_comp, ← rhoLin_mul, inv_mul_cancel, rhoLin_one,
          LinearMap.toMatrix'_id] }
  map_one' := Units.ext (by
    show LinearMap.toMatrix' (rhoLin hQN 1) = 1
    rw [rhoLin_one, LinearMap.toMatrix'_id])
  map_mul' g h := Units.ext (by
    show LinearMap.toMatrix' (rhoLin hQN (g * h)) =
      LinearMap.toMatrix' (rhoLin hQN g) * LinearMap.toMatrix' (rhoLin hQN h)
    rw [rhoLin_mul, LinearMap.toMatrix'_comp])

theorem rho_mulVec (g : N.Gz) (v : Fin 4 → ZMod 2) :
    ((rho hQN g : (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
      N.rhoFun g v := by
  show LinearMap.toMatrix' (rhoLin hQN g) *ᵥ v = _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem rho_mem (g : N.Gz) : rho hQN g ∈ orthQ0 := by
  rw [mem_orthQ0]
  intro v
  rw [rho_mulVec]
  exact rhoFun_q0 hQN g.2 v

@[expose] noncomputable def rho' : N.Gz →* orthQ0 :=
  (rho hQN).codRestrict orthQ0 (rho_mem hQN)

theorem rho'_mulVec (g : N.Gz) (v : Fin 4 → ZMod 2) :
    (((rho' hQN g : orthQ0) : (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = N.rhoFun g v :=
  rho_mulVec hQN g v

theorem comm_mem_of_ker {g : N.Gz} (hg : rho' hQN g = 1) {y : G} (hy : y ∈ N.Q)
    (hST : S ≤ T) (hTz : T ≤ N.Gz) :
    (g : G) * y * (g : G)⁻¹ * y⁻¹ ∈ Subgroup.zpowers (N.Φ (1, 0, 0)) := by
  have h1 : N.rhoFun g (N.δ y) = N.δ y := by
    rw [← rho'_mulVec hQN, hg]
    simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]
  rw [rhoFun_δ hQN g.2 hy] at h1
  have h2 := (N.δ_eq_iff hy (conj_mem_Q hQN g.2 hy)).mp h1.symm
  have hyz : y * N.Φ (1, 0, 0) = N.Φ (1, 0, 0) * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (hTz (N.Q_le hST hy))
  have e : (g : G) * y * (g : G)⁻¹ * y⁻¹ = y * (y⁻¹ * ((g : G) * y * (g : G)⁻¹)) * y⁻¹ := by
    group
  rw [e, conj_mem_zpowers hyz h2]
  exact h2

theorem false_of_normalizes_Q [Finite G] (hST : S ≤ T)
    (hT : quasithinIsSylowTwo T) (hTz : T ≤ N.Gz) (hVQ : conjClosure Z N.Gz = N.Q)
    (hC : ∀ g ∈ N.Gz, (∀ y ∈ Z, y * g = g * y) → g ∈ T)
    (hM1 : N.Gz ⊓ Subgroup.normalizer ((V₁ ⊓ N.Q : Subgroup G) : Set G) ≤ T) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZQ : ∀ c, N.Φ (c, 0, 0) ∈ N.Q := fun c => N.Φ_mem_Q (by norm_num) (by norm_num)
  have hZQ' : Z ≤ N.Q := fun g hg => by
    obtain ⟨c, rfl⟩ := (N.mem_Z g).mp hg
    exact hZQ c
  obtain ⟨ρ, hρ⟩ : ∃ ρ : N.Gz →* orthQ0, ρ = rho' hQN := ⟨_, rfl⟩
  set T' := T.subgroupOf N.Gz with hT'
  have hzX : ∀ g ∈ N.Gz, g * N.Φ (1, 0, 0) = N.Φ (1, 0, 0) * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have hK2 : IsPGroup 2 (zcommSub N.Gz N.Q (N.Φ (1, 0, 0)) hzX hQN) :=
    isPGroup_zcommSub N.z_mul_self hT.1 fun g hg => hC g (zcommSub_le (Subgroup.mem_inf.mp hg).1)
      fun y hy => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).2 y (hZQ' hy)
  have hKT' : zcommSub N.Gz N.Q (N.Φ (1, 0, 0)) hzX hQN ≤ T :=
    (le_pCoreOf_of_le_normalizer 2 zcommSub_le le_normalizer_zcommSub hK2).trans
      (EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_isSylowTwo hT hTz))
  have hKT : ρ.ker ≤ T' := fun g hg => by
    rw [hρ] at hg
    exact hKT' ⟨g.2, fun y hy => comm_mem_of_ker hQN (MonoidHom.mem_ker.mp hg) hy hST hTz⟩
  have hdvd1 : T'.index ∣ Nat.card ρ.range := by
    rw [← Subgroup.index_ker]
    exact Subgroup.index_dvd_of_le hKT
  have hdvd2 : Nat.card ρ.range ∣ 72 := by
    rw [← card_orthQ0]
    exact Subgroup.card_subgroup_dvd_card _
  have hodd : ¬ 2 ∣ T'.index := by
    intro h2
    apply hT.2
    exact h2.trans (Subgroup.relIndex_dvd_index_of_le hTz)
  set f : N.Gz → (Fin 4 → ZMod 2) := fun g => N.δ ((g : G) * N.Φ (F4.ω, 0, 0) * (g : G)⁻¹)
    with hf
  have hωQ : N.Φ (F4.ω, 0, 0) ∈ N.Q := hZQ _
  have hfT : ∀ g : N.Gz, ∀ t : N.Gz, t ∈ T' → f (g * t) = f g := by
    intro g t ht
    have htT : (t : G) ∈ T := ht
    show N.δ ((g : G) * t * N.Φ (F4.ω, 0, 0) * ((g : G) * t)⁻¹) =
      N.δ ((g : G) * N.Φ (F4.ω, 0, 0) * (g : G)⁻¹)
    have e : (g : G) * t * N.Φ (F4.ω, 0, 0) * ((g : G) * t)⁻¹ =
        (g : G) * ((t : G) * N.Φ (F4.ω, 0, 0) * (t : G)⁻¹) * (g : G)⁻¹ := by group
    rw [e]
    exact δ_conj_congr hQN g.2 (conj_mem_Q hQN t.2 hωQ) hωQ (N.δ_conj_ω hST htT)
  have hrange : Nat.card (Set.range f) ≤ T'.index := by
    let F : N.Gz ⧸ T' → (Fin 4 → ZMod 2) := Quotient.lift f fun a b hab => by
      have hab' : a⁻¹ * b ∈ T' := QuotientGroup.leftRel_apply.mp hab
      have e : b = a * (a⁻¹ * b) := by group
      rw [e, hfT a _ hab']
    have hFr : Set.range f = Set.range F := by
      ext v
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨QuotientGroup.mk g, rfl⟩
      · rintro ⟨q, rfl⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        exact ⟨g, rfl⟩
    rw [hFr]
    exact Finite.card_range_le F
  have hspan : Submodule.span (ZMod 2) (Set.range f) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : N.δ (N.sec v) = v := N.δ_sec v
    rw [← hv]
    have hsec : N.sec v ∈ conjClosure Z N.Gz := by
      rw [hVQ]
      exact N.sec_mem v
    have key : ∀ y ∈ conjClosure Z N.Gz, N.δ y ∈ Submodule.span (ZMod 2) (Set.range f) := by
      intro y hy
      have hyQ' : ∀ y ∈ conjClosure Z N.Gz, y ∈ N.Q := fun y hy => by
        rw [hVQ] at hy
        exact hy
      have hy' := hy
      unfold conjClosure at hy'
      clear hy
      induction hy' using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨h, hh, s, hs, rfl⟩ := hy
        have hhz : h * N.Φ (1, 0, 0) = N.Φ (1, 0, 0) * h :=
          Subgroup.mem_centralizer_singleton_iff.mp hh
        obtain ⟨c, rfl⟩ := (N.mem_Z s).mp hs
        rcases N.Z_cases c with hc | ⟨w, hw, hcw⟩
        · rw [conj_mem_zpowers hhz hc, (N.δ_eq_zero_iff (hZQ c)).mpr hc]
          exact Submodule.zero_mem _
        · have e : h * N.Φ (c, 0, 0) * h⁻¹ = (h * N.Φ (F4.ω, 0, 0) * h⁻¹) * w := by
            have hw' := conj_mem_zpowers hhz hw
            rw [hcw]
            calc h * (N.Φ (F4.ω, 0, 0) * w) * h⁻¹ =
                h * N.Φ (F4.ω, 0, 0) * h⁻¹ * (h * w * h⁻¹) := by group
              _ = h * N.Φ (F4.ω, 0, 0) * h⁻¹ * w := by rw [hw']
          rw [e, N.δ_mul (conj_mem_Q hQN hh hωQ) (N.zpowers_le_Q hw),
            (N.δ_eq_zero_iff (N.zpowers_le_Q hw)).mpr hw, add_zero]
          exact Submodule.subset_span ⟨⟨h, hh⟩, rfl⟩
      | one =>
        rw [N.δ_one]
        exact Submodule.zero_mem _
      | mul a b ha hb iha ihb =>
        rw [N.δ_mul (hyQ' a ha) (hyQ' b hb)]
        exact Submodule.add_mem _ iha ihb
      | inv a ha iha =>
        rw [N.δ_inv (hyQ' a ha)]
        exact iha
    exact key _ hsec
  have hge : 4 ≤ T'.index := by
    have : Fintype ↥(Set.range f) := Fintype.ofFinite _
    have h1 := finrank_span_le_card (R := ZMod 2) (Set.range f)
    rw [hspan, finrank_top, Module.finrank_pi, Fintype.card_fin, Set.toFinset_card,
      ← Nat.card_eq_fintype_card] at h1
    exact h1.trans hrange
  have h72 : T'.index ∣ 72 := hdvd1.trans hdvd2
  have h9 : T'.index = 9 := by
    have key : ∀ m, m ≤ 72 → m ∣ 72 → ¬ 2 ∣ m → 4 ≤ m → m = 9 := by decide
    exact key _ (Nat.le_of_dvd (by norm_num) h72) h72 hodd hge
  have h9' : 9 ∣ Nat.card ρ.range := h9 ▸ hdvd1
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (g3_mem_of_dvd h9')
  have hgv : ∀ v, N.rhoFun g v = g3 *ᵥ v := by
    intro v
    rw [← rho'_mulVec hQN, ← hρ, hg]
    rfl
  have hgv' : ∀ v, N.rhoFun (g⁻¹ : N.Gz) v = g3 *ᵥ (g3 *ᵥ v) := by
    intro v
    have h1 := rho'_mulVec hQN g⁻¹ v
    rw [map_inv, ← hρ, hg] at h1
    rw [← h1, mulVec_mulVec]
    show (g3 ^ 2) *ᵥ v = (g3 * g3) *ᵥ v
    rw [sq]
  have hW : ∀ k : N.Gz, (∀ v, v 1 = 0 → v 3 = 0 → N.rhoFun k v 1 = 0 ∧ N.rhoFun k v 3 = 0) →
      ∀ y ∈ V₁ ⊓ N.Q, (k : G) * y * (k : G)⁻¹ ∈ V₁ ⊓ N.Q := by
    intro k hk y hy
    obtain ⟨hyV, hyQ⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨c, a, rfl⟩ := (N.mem_V₁ y).mp hyV
    have hδ : N.δ (N.Φ (c, a, 0)) = ![f4re a, f4re 0, f4im c, 0] := N.δ_Φ c a 0
    have h1 : N.δ (N.Φ (c, a, 0)) 1 = 0 := by
      rw [hδ]
      exact f4re_zero
    have h3 : N.δ (N.Φ (c, a, 0)) 3 = 0 := by
      rw [hδ]
      rfl
    have hc := conj_mem_Q hQN k.2 hyQ
    have hk' := hk _ h1 h3
    rw [rhoFun_δ hQN k.2 hyQ] at hk'
    exact Subgroup.mem_inf.mpr ⟨N.mem_V₁_of_δ hc hk'.1 hk'.2, hc⟩
  have hgW := hW g fun v h1 h3 => by
    rw [hgv]
    exact g3_mulVec_mem v h1 h3
  have hgW' := hW g⁻¹ fun v h1 h3 => by
    rw [hgv']
    have h' := g3_mulVec_mem v h1 h3
    exact g3_mulVec_mem _ h'.1 h'.2
  have hgN : (g : G) ∈ Subgroup.normalizer ((V₁ ⊓ N.Q : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hgW y hy, fun hy => ?_⟩
    have h1 := hgW' _ hy
    have e : ((g⁻¹ : N.Gz) : G) * ((g : G) * y * (g : G)⁻¹) * ((g⁻¹ : N.Gz) : G)⁻¹ = y := by
      simp only [Subgroup.coe_inv, inv_inv]
      group
    rwa [e] at h1
  have hgT : (g : G) ∈ T := hM1 (Subgroup.mem_inf.mpr ⟨g.2, hgN⟩)
  obtain ⟨k, hk⟩ := hT.1 ⟨g, hgT⟩
  have hk' : g ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have h1 := congrArg Subtype.val hk
    simpa using h1
  have h1 := congrArg ρ hk'
  rw [map_pow, hg, map_one] at h1
  have hu3 : (⟨g3Unit, g3Unit_mem⟩ : orthQ0) ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    simp [g3Unit, g3_pow_three]
  have hu := eq_one_of_two_pow_of_odd h1 (by decide) hu3
  apply g3_ne_one
  have h2 := congrArg (fun u : orthQ0 => ((u : (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ) :
    Matrix (Fin 4) (Fin 4) (ZMod 2))) hu
  simpa [g3Unit] using h2

end ExcNF

end CFSG.Quasithin.H13.Sec53L3
