module

public import CFSG.RankThree.GF2n.Stroth80.DictModel
public import CFSG.RankThree.GF2n.Stroth80.Satz5Alg

public section

namespace CFSG.RankThree.GF2n.Stroth80.Satz5

open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim79
open scoped commutatorElement

variable {G : Type} [Group G] {P Z : Subgroup G} {K : Type} [Field K] {γ : G → K}

@[expose] def Induces (M₀ : Tim79.QuadModel P Z K γ) (g : G) (T : M₀.E → M₀.E) : Prop :=
  ∀ x ∈ P, M₀.π (g * x * g⁻¹) = T (M₀.π x)

structure Setting (M₀ : Tim79.QuadModel P Z K γ) (X : Subgroup G) (v₁ v₂ w₁ w₂ : M₀.E) :
    Prop where
  reg : Tim79.GammaReg P Z γ
  two : (2 : K) = 0
  b11 : M₀.B v₁ w₁ = 1
  b22 : M₀.B v₂ w₂ = 1
  b12 : M₀.B v₁ w₂ = 0
  b21 : M₀.B v₂ w₁ = 0
  vv : M₀.B v₁ v₂ = 0
  ww : M₀.B w₁ w₂ = 0
  norm : ∀ g ∈ X, ∀ x ∈ P, g * x * g⁻¹ ∈ P
  cent : ∀ g ∈ X, ∀ z ∈ Z, g * z * g⁻¹ = z
  faith : ∀ g ∈ X, (∀ x ∈ P, M₀.π (g * x * g⁻¹) = M₀.π x) →
    ∃ p ∈ P, ∀ x ∈ P, g * x * g⁻¹ = p * x * p⁻¹

@[expose] def rootA (M₀ : Tim79.QuadModel P Z K γ) (v₂ w₁ : M₀.E) (l : K) (e : M₀.E) : M₀.E :=
  e + (l * M₀.B e w₁) • v₂ + (l * M₀.B e v₂) • w₁

@[expose] def rootB (M₀ : Tim79.QuadModel P Z K γ) (v₁ v₂ : M₀.E) (m : K) (e : M₀.E) : M₀.E :=
  e + (m * M₀.B e v₂) • v₁ + (m * M₀.B e v₁) • v₂

theorem central_of_reg (M₀ : Tim79.QuadModel P Z K γ) (R : Tim79.GammaReg P Z γ) {z y : G}
    (hz : z ∈ Z) (hy : y ∈ P) : z * y = y * z := by
  refine (M₀.comm_iff_B R (R.V_le hz) hy).mpr ?_
  rw [(M₀.π_ker z (R.V_le hz)).mpr hz, map_zero, LinearMap.zero_apply]

section Setting

variable {M₀ : Tim79.QuadModel P Z K γ} {X : Subgroup G} {v₁ v₂ w₁ w₂ : M₀.E}

theorem Setting.sym (S : Setting M₀ X v₁ v₂ w₁ w₂) (e f : M₀.E) : M₀.B e f = M₀.B f e := by
  linear_combination Tim79.QuadModel.B_comm (M₀ := M₀) e f - (M₀.B f e) * S.two

theorem Setting.central (S : Setting M₀ X v₁ v₂ w₁ w₂) {z y : G} (hz : z ∈ Z) (hy : y ∈ P) :
    z * y = y * z :=
  central_of_reg M₀ S.reg hz hy

theorem Setting.bw1v1 (S : Setting M₀ X v₁ v₂ w₁ w₂) : M₀.B w₁ v₁ = 1 := by rw [S.sym, S.b11]
theorem Setting.bw2v2 (S : Setting M₀ X v₁ v₂ w₁ w₂) : M₀.B w₂ v₂ = 1 := by rw [S.sym, S.b22]
theorem Setting.bw2v1 (S : Setting M₀ X v₁ v₂ w₁ w₂) : M₀.B w₂ v₁ = 0 := by rw [S.sym, S.b12]
theorem Setting.bw1v2 (S : Setting M₀ X v₁ v₂ w₁ w₂) : M₀.B w₁ v₂ = 0 := by rw [S.sym, S.b21]
theorem Setting.bv2v1 (S : Setting M₀ X v₁ v₂ w₁ w₂) : M₀.B v₂ v₁ = 0 := by rw [S.sym, S.vv]
theorem Setting.bw2w1 (S : Setting M₀ X v₁ v₂ w₁ w₂) : M₀.B w₂ w₁ = 0 := by rw [S.sym, S.ww]

theorem Setting.add_self (S : Setting M₀ X v₁ v₂ w₁ w₂) (u : M₀.E) : u + u = 0 := by
  rw [← two_smul K u, S.two, zero_smul]

theorem Setting.rootA_rootA (S : Setting M₀ X v₁ v₂ w₁ w₂) (l : K) (e : M₀.E) :
    rootA M₀ v₂ w₁ l (rootA M₀ v₂ w₁ l e) = e := by
  have h1 : M₀.B (rootA M₀ v₂ w₁ l e) w₁ = M₀.B e w₁ := by
    simp only [rootA, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      S.b21, M₀.alt]
    ring
  have h2 : M₀.B (rootA M₀ v₂ w₁ l e) v₂ = M₀.B e v₂ := by
    simp only [rootA, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      S.bw1v2, M₀.alt]
    ring
  calc rootA M₀ v₂ w₁ l (rootA M₀ v₂ w₁ l e)
      = (e + (l * M₀.B e w₁) • v₂ + (l * M₀.B e v₂) • w₁) + (l * M₀.B e w₁) • v₂
          + (l * M₀.B e v₂) • w₁ := by
        rw [rootA, h1, h2]; rfl
    _ = e + ((l * M₀.B e w₁) • v₂ + (l * M₀.B e w₁) • v₂)
          + ((l * M₀.B e v₂) • w₁ + (l * M₀.B e v₂) • w₁) := by abel
    _ = e := by rw [S.add_self, S.add_self, add_zero, add_zero]

theorem Setting.rootB_rootB (S : Setting M₀ X v₁ v₂ w₁ w₂) (m : K) (e : M₀.E) :
    rootB M₀ v₁ v₂ m (rootB M₀ v₁ v₂ m e) = e := by
  have h1 : M₀.B (rootB M₀ v₁ v₂ m e) v₂ = M₀.B e v₂ := by
    simp only [rootB, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      S.vv, M₀.alt]
    ring
  have h2 : M₀.B (rootB M₀ v₁ v₂ m e) v₁ = M₀.B e v₁ := by
    simp only [rootB, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      S.bv2v1, M₀.alt]
    ring
  calc rootB M₀ v₁ v₂ m (rootB M₀ v₁ v₂ m e)
      = (e + (m * M₀.B e v₂) • v₁ + (m * M₀.B e v₁) • v₂) + (m * M₀.B e v₂) • v₁
          + (m * M₀.B e v₁) • v₂ := by
        rw [rootB, h1, h2]; rfl
    _ = e + ((m * M₀.B e v₂) • v₁ + (m * M₀.B e v₂) • v₁)
          + ((m * M₀.B e v₁) • v₂ + (m * M₀.B e v₁) • v₂) := by abel
    _ = e := by rw [S.add_self, S.add_self, add_zero, add_zero]

theorem Setting.rootA_rootB (S : Setting M₀ X v₁ v₂ w₁ w₂) (l m : K) (e : M₀.E) :
    rootA M₀ v₂ w₁ l (rootB M₀ v₁ v₂ m e) = rootB M₀ v₁ v₂ m (rootA M₀ v₂ w₁ l e) := by
  have h1 : M₀.B (rootB M₀ v₁ v₂ m e) w₁ = M₀.B e w₁ + m * M₀.B e v₂ := by
    simp only [rootB, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      S.b11, S.b21, M₀.alt]
    ring
  have h2 : M₀.B (rootB M₀ v₁ v₂ m e) v₂ = M₀.B e v₂ := by
    simp only [rootB, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      S.vv, M₀.alt]
    ring
  have h3 : M₀.B (rootA M₀ v₂ w₁ l e) v₂ = M₀.B e v₂ := by
    simp only [rootA, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      S.bw1v2, M₀.alt]
    ring
  have h4 : M₀.B (rootA M₀ v₂ w₁ l e) v₁ = M₀.B e v₁ + l * M₀.B e v₂ := by
    simp only [rootA, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      S.bv2v1, S.bw1v1, M₀.alt]
    ring
  simp only [rootA, rootB, h1, h2, h3, h4, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, S.bw1v2, S.b21, S.b11, S.bw1v1, S.vv, S.bv2v1, M₀.alt]
  module

theorem Setting.rootA_v₁ (S : Setting M₀ X v₁ v₂ w₁ w₂) (l t : K) :
    rootA M₀ v₂ w₁ l (t • v₁) = t • v₁ + (l * t) • v₂ := by
  simp [rootA, S.b11, S.vv]

theorem Setting.rootA_w₂ (S : Setting M₀ X v₁ v₂ w₁ w₂) (l s : K) :
    rootA M₀ v₂ w₁ l (s • w₂) = s • w₂ + (l * s) • w₁ := by
  simp [rootA, S.bw2w1, S.bw2v2]

theorem Setting.rootB_w₂ (S : Setting M₀ X v₁ v₂ w₁ w₂) (m s : K) :
    rootB M₀ v₁ v₂ m (s • w₂) = s • w₂ + (m * s) • v₁ := by
  simp [rootB, S.bw2v2, S.bw2v1]

theorem Setting.rootB_w₁ (S : Setting M₀ X v₁ v₂ w₁ w₂) (m t : K) :
    rootB M₀ v₁ v₂ m (t • w₁) = t • w₁ + (m * t) • v₂ := by
  simp [rootB, S.bw1v2, S.bw1v1]

theorem Setting.induces_inv (S : Setting M₀ X v₁ v₂ w₁ w₂) {g : G} (hg : g ∈ X)
    {T : M₀.E → M₀.E} (hT : Induces M₀ g T) (hTT : ∀ e, T (T e) = e) :
    Induces M₀ g⁻¹ T := by
  intro x hx
  have hy : g⁻¹ * x * g⁻¹⁻¹ ∈ P := S.norm g⁻¹ (X.inv_mem hg) x hx
  have h := hT _ hy
  have h' : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
  rw [h'] at h
  rw [h, hTT]

theorem Setting.comm_inner (S : Setting M₀ X v₁ v₂ w₁ w₂) {a b : G} (ha : a ∈ X) (hb : b ∈ X)
    {l m : K} (hA : Induces M₀ a (rootA M₀ v₂ w₁ l)) (hB : Induces M₀ b (rootB M₀ v₁ v₂ m)) :
    ∃ p ∈ P, ∀ x ∈ P, ((b * a)⁻¹ * (a * b)) * x * ((b * a)⁻¹ * (a * b))⁻¹ = p * x * p⁻¹ := by
  have hAi : Induces M₀ a⁻¹ (rootA M₀ v₂ w₁ l) :=
    S.induces_inv ha hA (S.rootA_rootA l)
  have hBi : Induces M₀ b⁻¹ (rootB M₀ v₁ v₂ m) :=
    S.induces_inv hb hB (S.rootB_rootB m)
  refine S.faith _ (X.mul_mem (X.inv_mem (X.mul_mem hb ha)) (X.mul_mem ha hb)) fun x hx => ?_
  have hx₁ := S.norm b hb x hx
  have hx₂ := S.norm a ha _ hx₁
  have hx₃ := S.norm b⁻¹ (X.inv_mem hb) _ hx₂
  have e1 : M₀.π (b * x * b⁻¹) = rootB M₀ v₁ v₂ m (M₀.π x) := hB x hx
  have e2 : M₀.π (a * (b * x * b⁻¹) * a⁻¹) = rootA M₀ v₂ w₁ l (rootB M₀ v₁ v₂ m (M₀.π x)) := by
    rw [hA _ hx₁, e1]
  have e3 : M₀.π (b⁻¹ * (a * (b * x * b⁻¹) * a⁻¹) * b⁻¹⁻¹) =
      rootB M₀ v₁ v₂ m (rootA M₀ v₂ w₁ l (rootB M₀ v₁ v₂ m (M₀.π x))) := by
    rw [hBi _ hx₂, e2]
  have e4 : M₀.π (a⁻¹ * (b⁻¹ * (a * (b * x * b⁻¹) * a⁻¹) * b⁻¹⁻¹) * a⁻¹⁻¹) =
      rootA M₀ v₂ w₁ l (rootB M₀ v₁ v₂ m (rootA M₀ v₂ w₁ l (rootB M₀ v₁ v₂ m (M₀.π x)))) := by
    rw [hAi _ hx₃, e3]
  have e5 : (b * a)⁻¹ * (a * b) * x * ((b * a)⁻¹ * (a * b))⁻¹ =
      a⁻¹ * (b⁻¹ * (a * (b * x * b⁻¹) * a⁻¹) * b⁻¹⁻¹) * a⁻¹⁻¹ := by group
  rw [e5, e4, S.rootA_rootB l m (rootA M₀ v₂ w₁ l (rootB M₀ v₁ v₂ m (M₀.π x))),
    S.rootA_rootA, S.rootB_rootB]

theorem Setting.exists_corr (S : Setting M₀ X v₁ v₂ w₁ w₂) {p r : G} (hp : p ∈ P) (hr : r ∈ P)
    (h : M₀.π p = M₀.π r) : ∃ k ∈ Z, r = p * k :=
  ⟨p⁻¹ * r, (Tim79.QuadModel.pi_eq_iff M₀ hp hr).mp h, by group⟩

theorem Setting.exists_corr_conj (S : Setting M₀ X v₁ v₂ w₁ w₂) {g : G} (hg : g ∈ X)
    {T : M₀.E → M₀.E} (hT : Induces M₀ g T) {x y : G} (hx : x ∈ P) (hy : y ∈ P)
    (h : T (M₀.π x) = M₀.π y) : ∃ k ∈ Z, g * x * g⁻¹ = y * k :=
  S.exists_corr hy (S.norm g hg x hx) (by rw [hT x hx, h])

structure Lifts (M₀ : Tim79.QuadModel P Z K γ) (v₁ v₂ w₁ w₂ : M₀.E) where
  xs : K → G
  ys : K → G
  zs : K → G
  vs : K → G
  xs_mem : ∀ s, xs s ∈ P
  ys_mem : ∀ s, ys s ∈ P
  zs_mem : ∀ s, zs s ∈ P
  vs_mem : ∀ s, vs s ∈ P
  xs_pi : ∀ s, M₀.π (xs s) = s • w₂
  ys_pi : ∀ s, M₀.π (ys s) = s • v₁
  zs_pi : ∀ s, M₀.π (zs s) = s • w₁
  vs_pi : ∀ s, M₀.π (vs s) = s • v₂

theorem Lifts.nonempty (M₀ : Tim79.QuadModel P Z K γ) (v₁ v₂ w₁ w₂ : M₀.E) :
    Nonempty (Lifts M₀ v₁ v₂ w₁ w₂) := by
  choose xs hxs using fun s : K => M₀.π_surj (s • w₂)
  choose ys hys using fun s : K => M₀.π_surj (s • v₁)
  choose zs hzs using fun s : K => M₀.π_surj (s • w₁)
  choose vs hvs using fun s : K => M₀.π_surj (s • v₂)
  exact ⟨⟨xs, ys, zs, vs, fun s => (hxs s).1, fun s => (hys s).1, fun s => (hzs s).1,
    fun s => (hvs s).1, fun s => (hxs s).2, fun s => (hys s).2, fun s => (hzs s).2,
    fun s => (hvs s).2⟩⟩

theorem Setting.gamma_mul4 (S : Setting M₀ X v₁ v₂ w₁ w₂) {a b c d : G} (ha : a ∈ Z) (hb : b ∈ Z)
    (hc : c ∈ Z) (hd : d ∈ Z) : γ (a * b * c * d) = γ a + γ b + γ c + γ d := by
  rw [S.reg.add _ (Z.mul_mem (Z.mul_mem ha hb) hc) d hd,
    S.reg.add _ (Z.mul_mem ha hb) c hc, S.reg.add a ha b hb]

theorem Setting.exists_Fk (S : Setting M₀ X v₁ v₂ w₁ w₂) (L : Lifts M₀ v₁ v₂ w₁ w₂) {a : G}
    (ha : a ∈ X) {l : K} (hA : Induces M₀ a (rootA M₀ v₂ w₁ l)) :
    ∃ Fk : K → G, ∀ t, Fk t ∈ Z ∧ a * L.ys t * a⁻¹ = L.ys t * L.vs (l * t) * Fk t := by
  have h : ∀ t, ∃ k ∈ Z, a * L.ys t * a⁻¹ = L.ys t * L.vs (l * t) * k := fun t => by
    refine S.exists_corr_conj ha hA (L.ys_mem t) (P.mul_mem (L.ys_mem t) (L.vs_mem _)) ?_
    rw [L.ys_pi, S.rootA_v₁, M₀.π_mul _ (L.ys_mem t) _ (L.vs_mem _), L.ys_pi, L.vs_pi]
  choose Fk hFk using h
  exact ⟨Fk, hFk⟩

theorem Setting.exists_Hk (S : Setting M₀ X v₁ v₂ w₁ w₂) (L : Lifts M₀ v₁ v₂ w₁ w₂) {b : G}
    (hb : b ∈ X) {m : K} (hB : Induces M₀ b (rootB M₀ v₁ v₂ m)) :
    ∃ Hk : K → G, ∀ t, Hk t ∈ Z ∧ b * L.zs t * b⁻¹ = L.zs t * L.vs (m * t) * Hk t := by
  have h : ∀ t, ∃ k ∈ Z, b * L.zs t * b⁻¹ = L.zs t * L.vs (m * t) * k := fun t => by
    refine S.exists_corr_conj hb hB (L.zs_mem t) (P.mul_mem (L.zs_mem t) (L.vs_mem _)) ?_
    rw [L.zs_pi, S.rootB_w₁, M₀.π_mul _ (L.zs_mem t) _ (L.vs_mem _), L.zs_pi, L.vs_pi]
  choose Hk hHk using h
  exact ⟨Hk, hHk⟩

theorem Setting.key (S : Setting M₀ X v₁ v₂ w₁ w₂) (L : Lifts M₀ v₁ v₂ w₁ w₂) {a b : G}
    (ha : a ∈ X) (hb : b ∈ X) {l m : K} (hA : Induces M₀ a (rootA M₀ v₂ w₁ l))
    (hB : Induces M₀ b (rootB M₀ v₁ v₂ m)) {Fk Hk : K → G}
    (hF : ∀ t, Fk t ∈ Z ∧ a * L.ys t * a⁻¹ = L.ys t * L.vs (l * t) * Fk t)
    (hH : ∀ t, Hk t ∈ Z ∧ b * L.zs t * b⁻¹ = L.zs t * L.vs (m * t) * Hk t) :
    ∃ κ₀ : K, ∀ s, l * m * s ^ 2 + γ (Fk (m * s)) + γ (Hk (l * s)) = κ₀ * s := by
  obtain ⟨c, hc⟩ : ∃ c : G, c = (b * a)⁻¹ * (a * b) := ⟨_, rfl⟩
  obtain ⟨p, hpP, hp⟩ := S.comm_inner ha hb hA hB
  rw [← hc] at hp
  refine ⟨M₀.B (M₀.π p) w₂, fun s => ?_⟩
  obtain ⟨k₁, hk₁Z, hk₁⟩ : ∃ k ∈ Z, a * L.xs s * a⁻¹ = L.xs s * L.zs (l * s) * k := by
    refine S.exists_corr_conj ha hA (L.xs_mem s) (P.mul_mem (L.xs_mem s) (L.zs_mem _)) ?_
    rw [L.xs_pi, S.rootA_w₂, M₀.π_mul _ (L.xs_mem s) _ (L.zs_mem _), L.xs_pi, L.zs_pi]
  obtain ⟨k₂, hk₂Z, hk₂⟩ : ∃ k ∈ Z, b * L.xs s * b⁻¹ = L.xs s * L.ys (m * s) * k := by
    refine S.exists_corr_conj hb hB (L.xs_mem s) (P.mul_mem (L.xs_mem s) (L.ys_mem _)) ?_
    rw [L.xs_pi, S.rootB_w₂, M₀.π_mul _ (L.xs_mem s) _ (L.ys_mem _), L.xs_pi, L.ys_pi]
  obtain ⟨hk₃Z, hk₃⟩ := hF (m * s)
  obtain ⟨hk₄Z, hk₄⟩ := hH (l * s)
  rw [mul_left_comm m l s] at hk₄
  have hxP := L.xs_mem s
  have hyP := L.ys_mem (m * s)
  have hzP := L.zs_mem (l * s)
  have hvP := L.vs_mem (l * (m * s))
  have hκ : ⁅L.zs (l * s), L.ys (m * s)⁆ ∈ Z := M₀.comm_mem _ hzP _ hyP
  have hκ' : ⁅p, L.xs s⁆ ∈ Z := M₀.comm_mem _ hpP _ hxP
  have hzy : L.zs (l * s) * L.ys (m * s) =
      L.ys (m * s) * L.zs (l * s) * ⁅L.zs (l * s), L.ys (m * s)⁆ := by
    have h1 : L.zs (l * s) * L.ys (m * s) =
        ⁅L.zs (l * s), L.ys (m * s)⁆ * (L.ys (m * s) * L.zs (l * s)) := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact S.central hκ (P.mul_mem hyP hzP)
  have hcx : c * L.xs s * c⁻¹ = L.xs s * ⁅p, L.xs s⁆ := by
    have h1 : c * L.xs s * c⁻¹ = ⁅p, L.xs s⁆ * L.xs s := by
      rw [hp _ hxP]
      simp only [commutatorElement_def]; group
    rw [h1]
    exact S.central hκ' hxP
  have rel := commutator_relation a b c (L.xs s) (L.ys (m * s)) (L.zs (l * s))
    (L.vs (l * (m * s))) k₁ k₂ (Fk (m * s)) (Hk (l * s)) ⁅L.zs (l * s), L.ys (m * s)⁆
    ⁅p, L.xs s⁆ (by rw [hc]; group) hk₁ hk₂ hk₃ hk₄ hzy hcx
    (S.cent a ha _ hk₂Z) (S.cent a ha _ hκ') (S.cent b hb _ hk₁Z) (S.cent b hb _ hκ')
    (S.central hk₁Z hyP) (S.central hk₁Z hvP) (S.central hκ hvP)
    (S.central hk₂Z hzP) (S.central hk₂Z hvP)
  have hg := congrArg γ rel
  rw [S.gamma_mul4 hκ hk₁Z hk₃Z hk₂Z, S.gamma_mul4 hk₂Z hk₄Z hk₁Z hκ'] at hg
  have g1 : γ ⁅L.zs (l * s), L.ys (m * s)⁆ = l * m * s ^ 2 := by
    rw [M₀.comm_eq _ hzP _ hyP, L.zs_pi, L.ys_pi]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, S.bw1v1]
    ring
  have g2 : γ ⁅p, L.xs s⁆ = M₀.B (M₀.π p) w₂ * s := by
    rw [M₀.comm_eq _ hpP _ hxP, L.xs_pi]
    simp only [map_smul, smul_eq_mul]
    ring
  rw [g1, g2] at hg
  linear_combination hg + (γ (Hk (l * s))) * S.two

theorem Setting.false_of_rootLifts (S : Setting M₀ X v₁ v₂ w₁ w₂) {ν : K} (hν0 : ν ≠ 0)
    (hν1 : ν ≠ 1) (hA : ∀ l : K, (l = 1 ∨ l = ν) → ∃ a ∈ X, Induces M₀ a (rootA M₀ v₂ w₁ l))
    (hB : ∀ m : K, (m = 1 ∨ m = ν) → ∃ b ∈ X, Induces M₀ b (rootB M₀ v₁ v₂ m)) : False := by
  obtain ⟨L⟩ := Lifts.nonempty M₀ v₁ v₂ w₁ w₂
  obtain ⟨a₁, ha₁, hA₁⟩ := hA 1 (Or.inl rfl)
  obtain ⟨aν, haν, hAν⟩ := hA ν (Or.inr rfl)
  obtain ⟨b₁, hb₁, hB₁⟩ := hB 1 (Or.inl rfl)
  obtain ⟨bν, hbν, hBν⟩ := hB ν (Or.inr rfl)
  obtain ⟨F₁, hF₁⟩ := S.exists_Fk L ha₁ hA₁
  obtain ⟨Fν, hFν⟩ := S.exists_Fk L haν hAν
  obtain ⟨H₁, hH₁⟩ := S.exists_Hk L hb₁ hB₁
  obtain ⟨Hν, hHν⟩ := S.exists_Hk L hbν hBν
  exact elimination S.two hν0 hν1 (fun t => γ (F₁ t)) (fun t => γ (Fν t))
    (fun t => γ (H₁ t)) (fun t => γ (Hν t))
    (S.key L ha₁ hb₁ hA₁ hB₁ hF₁ hH₁) (S.key L haν hb₁ hAν hB₁ hFν hH₁)
    (S.key L ha₁ hbν hA₁ hBν hF₁ hHν) (S.key L haν hbν hAν hBν hFν hHν)

end Setting

end CFSG.RankThree.GF2n.Stroth80.Satz5
