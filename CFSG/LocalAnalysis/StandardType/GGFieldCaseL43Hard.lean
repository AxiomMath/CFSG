module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL43Prod
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type*} [Group G]

theorem conj_mul_inv_mem_of_pow_normalizes [Finite G] {p : ℕ} [Fact p.Prime]
    {V H : Subgroup G} {x g : G} (hV : IsElemAbelian p V) (hHV : H ≤ V) (hxV : x ∈ V)
    (hVeq : V = H ⊔ Subgroup.zpowers x) (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgH : ∀ h ∈ H, g * h * g⁻¹ ∈ H) {k : ℕ} (hgk : g ^ p ^ k * x = x * g ^ p ^ k) :
    g * x * g⁻¹ * x⁻¹ ∈ H := by
  have hxB : ∀ b ∈ H, x * b = b * x := fun b hb => mul_comm_of_isElemAbelian hV hxV (hHV hb)
  have hcV : g * x * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hgV x).mp hxV
  obtain ⟨b, hb, j, hc⟩ := exists_mem_mul_pow_of_mem_sup hxB (hVeq ▸ hcV)
  have hiter : ∀ n : ℕ, ∃ b' ∈ H, g ^ n * x * (g ^ n)⁻¹ = b' * x ^ (j ^ n) := by
    intro n
    induction n with
    | zero => exact ⟨1, H.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨b', hb', h'⟩ := ih
      refine ⟨(g * b' * g⁻¹) * b ^ (j ^ n), H.mul_mem (hgH b' hb') (H.pow_mem hb _), ?_⟩
      have hcomm : Commute b (x ^ j) :=
        mul_comm_of_isElemAbelian hV (hHV hb) (V.pow_mem hxV j)
      calc g ^ (n + 1) * x * (g ^ (n + 1))⁻¹ = g * (g ^ n * x * (g ^ n)⁻¹) * g⁻¹ := by
              rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
        _ = (g * b' * g⁻¹) * (g * x * g⁻¹) ^ (j ^ n) := by
              rw [h', conj_pow]; simp only [mul_assoc, inv_mul_cancel_left]
        _ = (g * b' * g⁻¹) * b ^ (j ^ n) * x ^ (j ^ (n + 1)) := by
              rw [hc, hcomm.mul_pow, ← pow_mul, pow_succ']; simp only [mul_assoc]
  obtain ⟨b', hb', h'⟩ := hiter (p ^ k)
  have hxp : x ^ p = 1 := hV.2 x hxV
  have hjmod : x ^ (j ^ p ^ k) = x ^ j := by
    have hz : ((j ^ p ^ k : ℕ) : ZMod p) = (j : ZMod p) := by
      push_cast
      exact ZMod.pow_card_pow (p := p) _
    rw [pow_eq_pow_mod_of_pow_eq_one hxp, pow_eq_pow_mod_of_pow_eq_one hxp j,
      (ZMod.natCast_eq_natCast_iff' _ _ _).mp hz]
  have hx' : x = b' * x ^ j := by
    rw [← hjmod, ← h', hgk, mul_inv_cancel_right]
  have hcx : g * x * g⁻¹ * x⁻¹ = b * b'⁻¹ := by
    calc g * x * g⁻¹ * x⁻¹ = (b * x ^ j) * (b' * x ^ j)⁻¹ := by rw [← hc, ← hx']
      _ = b * b'⁻¹ := by group
  rw [hcx]
  exact H.mul_mem hb (H.inv_mem hb')

theorem triv_mod_mul {V B₁ : Subgroup G} {g h : G} (hgB : ∀ b ∈ B₁, g * b * g⁻¹ ∈ B₁)
    (hg : ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ B₁) (hh : ∀ v ∈ V, h * v * h⁻¹ * v⁻¹ ∈ B₁) : ∀ v ∈ V, g * h * v * (g * h)⁻¹ * v⁻¹ ∈ B₁ := by
  intro v hv
  have e : g * h * v * (g * h)⁻¹ * v⁻¹ =
      (g * (h * v * h⁻¹ * v⁻¹) * g⁻¹) * (g * v * g⁻¹ * v⁻¹) := by group
  rw [e]
  exact B₁.mul_mem (hgB _ (hh v hv)) (hg v hv)

theorem triv_mod_inv {V B₁ : Subgroup G} {g : G} (hgV : ∀ v ∈ V, g⁻¹ * v * g ∈ V)
    (hg : ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ B₁) : ∀ v ∈ V, g⁻¹ * v * g⁻¹⁻¹ * v⁻¹ ∈ B₁ := by
  intro v hv
  have h1 := B₁.inv_mem (hg _ (hgV v hv))
  have e : (g * (g⁻¹ * v * g) * g⁻¹ * (g⁻¹ * v * g)⁻¹)⁻¹ = g⁻¹ * v * g⁻¹⁻¹ * v⁻¹ := by group
  rwa [e] at h1

theorem triv_mod_conj {V B₁ : Subgroup G} {g n : G} (hgV : ∀ v ∈ V, g⁻¹ * v * g ∈ V)
    (hgB : ∀ b ∈ B₁, g * b * g⁻¹ ∈ B₁) (hn : ∀ v ∈ V, n * v * n⁻¹ * v⁻¹ ∈ B₁) :
    ∀ v ∈ V, g * n * g⁻¹ * v * (g * n * g⁻¹)⁻¹ * v⁻¹ ∈ B₁ := by
  intro v hv
  have h1 := hgB _ (hn _ (hgV v hv))
  have e : g * (n * (g⁻¹ * v * g) * n⁻¹ * (g⁻¹ * v * g)⁻¹) * g⁻¹ =
      g * n * g⁻¹ * v * (g * n * g⁻¹)⁻¹ * v⁻¹ := by group
  rwa [e] at h1

theorem comm_mul_right_eq {V B₁ : Subgroup G} {p : ℕ} (hV : IsElemAbelian p V) (hB₁V : B₁ ≤ V)
    {g v w : G} (hv : v ∈ V) (hgw : g * w * g⁻¹ * w⁻¹ ∈ B₁)
    (hgvV : g * v * g⁻¹ ∈ V) :
    g * (v * w) * g⁻¹ * (v * w)⁻¹ = (g * v * g⁻¹ * v⁻¹) * (g * w * g⁻¹ * w⁻¹) := by
  have hc : (g * w * g⁻¹ * w⁻¹) * v = v * (g * w * g⁻¹ * w⁻¹) :=
    mul_comm_of_isElemAbelian hV (hB₁V hgw) hv
  have hc' : (g * w * g⁻¹ * w⁻¹) * (g * v * g⁻¹) = (g * v * g⁻¹) * (g * w * g⁻¹ * w⁻¹) :=
    mul_comm_of_isElemAbelian hV (hB₁V hgw) hgvV
  calc g * (v * w) * g⁻¹ * (v * w)⁻¹
      = (g * v * g⁻¹) * (g * w * g⁻¹ * w⁻¹) * v⁻¹ := by group
    _ = (g * w * g⁻¹ * w⁻¹) * (g * v * g⁻¹) * v⁻¹ := by rw [hc']
    _ = (g * v * g⁻¹ * v⁻¹) * (g * w * g⁻¹ * w⁻¹) := by
        have : (g * w * g⁻¹ * w⁻¹) * (g * v * g⁻¹) * v⁻¹ =
            (g * v * g⁻¹) * ((g * w * g⁻¹ * w⁻¹) * v⁻¹) := by rw [hc']; group
        rw [this]
        have hc2 : (g * w * g⁻¹ * w⁻¹) * v⁻¹ = v⁻¹ * (g * w * g⁻¹ * w⁻¹) := by
          have := congrArg (fun t => v⁻¹ * t * v⁻¹) hc
          simpa [mul_assoc] using this.symm
        rw [hc2]
        group

end General

section

variable {G : Type*} [Group G]

theorem isElemAbelian_of_le {p : ℕ} {V W : Subgroup G} (hV : IsElemAbelian p V) (hW : W ≤ V) :
    IsElemAbelian p W := CFSG.Open.IsElemAbelian.mono hV hW

theorem hard_exists_comm [Finite G] {p : ℕ} [Fact p.Prime] {V X N B₁ : Subgroup G} {x : G}
    (hV : IsElemAbelian p V) (hxV : x ∈ V)
    (hCB₁ : ∀ v ∈ V, (∀ g ∈ X, g * v = v * g) → v ∈ B₁)
    (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (hXp : ∀ g ∈ X, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (V : Set G))
    (hNx : ∀ n ∈ N, n * x = x * n) (hxB₁ : x ∉ B₁)
    (hCN : ∀ v ∈ V, (∀ n ∈ N, n * v = v * n) → v ∈ Subgroup.zpowers x) :
    ∃ g ∈ X, ∃ n ∈ N, g * n * g⁻¹ * n⁻¹ ∉ Subgroup.centralizer (V : Set G) := by
  by_contra hcon
  push Not at hcon
  have hXV : ∀ g ∈ X, ∀ v ∈ V, g * v * g⁻¹ ∈ V := fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hXN hg) v).mp hv
  have hz : ∀ g ∈ X, g * x * g⁻¹ ∈ Subgroup.zpowers x := by
    intro g hg
    refine hCN _ (hXV g hg x hxV) (fun n hn => ?_)
    have hc' : n * g * n⁻¹ * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      have h1 := Subgroup.inv_mem _ (hcon g hg n hn)
      have e : (g * n * g⁻¹ * n⁻¹)⁻¹ = n * g * n⁻¹ * g⁻¹ := by group
      rwa [e] at h1
    have hcz := Subgroup.mem_centralizer_iff.mp hc' (g * x * g⁻¹) (hXV g hg x hxV)
    have hnx : n * x * n⁻¹ = x := by rw [hNx n hn, mul_inv_cancel_right]
    calc n * (g * x * g⁻¹)
        = (n * g * n⁻¹ * g⁻¹) * (g * (n * x * n⁻¹) * g⁻¹) * (n * g * n⁻¹ * g⁻¹)⁻¹ * n := by
          group
      _ = (n * g * n⁻¹ * g⁻¹) * (g * x * g⁻¹) * (n * g * n⁻¹ * g⁻¹)⁻¹ * n := by rw [hnx]
      _ = (g * x * g⁻¹) * n := by rw [← hcz]; group
  apply hxB₁
  refine hCB₁ x hxV (fun g hg => ?_)
  have hZV : Subgroup.zpowers x ≤ V := Subgroup.zpowers_le.mpr hxV
  have hgZ : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    apply mem_normalizer_of_forall_conj_mem
    intro w hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have h1 := hz g⁻¹ (X.inv_mem hg)
    rw [inv_inv] at h1
    have e : g⁻¹ * x ^ i * g = (g⁻¹ * x * g⁻¹⁻¹) ^ i := by rw [conj_zpow, inv_inv]
    rw [e, inv_inv]
    exact Subgroup.zpow_mem _ h1 i
  obtain ⟨k, hk⟩ := hXp g hg
  have hgk : g ^ p ^ k * x = x * g ^ p ^ k :=
    (Subgroup.mem_centralizer_iff.mp hk x hxV).symm
  have h1 := conj_mul_inv_mem_of_pow_centralizes (isElemAbelian_of_le hV hZV) bot_le
    (Subgroup.mem_zpowers x) (by rw [bot_sup_eq]) hgZ (fun b hb => by
      rw [Subgroup.mem_bot.mp hb, mul_one, one_mul]) hgk
  rw [Subgroup.mem_bot] at h1
  calc g * x = g * x * g⁻¹ * x⁻¹ * x * g := by group
    _ = x * g := by rw [h1, one_mul]

end

section

variable {G : Type*} [Group G]

theorem triv_mod_of_gen {p : ℕ} {V B₁ : Subgroup G} {x d h : G} (hV : IsElemAbelian p V)
    (hB₁V : B₁ ≤ V) (hxV : x ∈ V) (hdV : d ∈ V)
    (hVgen : V = (B₁ ⊔ Subgroup.zpowers x) ⊔ Subgroup.zpowers d)
    (hhV : ∀ v ∈ V, h * v * h⁻¹ ∈ V) (hhB : ∀ b ∈ B₁, h * b = b * h)
    (hx : h * x * h⁻¹ * x⁻¹ ∈ B₁) (hd : h * d * h⁻¹ * d⁻¹ ∈ B₁) :
    ∀ v ∈ V, h * v * h⁻¹ * v⁻¹ ∈ B₁ := by
  let S : Subgroup G :=
    { carrier := {v | v ∈ V ∧ h * v * h⁻¹ * v⁻¹ ∈ B₁}
      mul_mem' := fun {a b} ha hb => ⟨V.mul_mem ha.1 hb.1, by
        rw [comm_mul_right_eq hV hB₁V ha.1 hb.2 (hhV a ha.1)]
        exact B₁.mul_mem ha.2 hb.2⟩
      one_mem' := ⟨V.one_mem, by simp⟩
      inv_mem' := fun {a} ha => ⟨V.inv_mem ha.1, by
        have hc : Commute (h * a * h⁻¹ * a⁻¹) a := mul_comm_of_isElemAbelian hV (hB₁V ha.2) ha.1
        have e : h * a⁻¹ * h⁻¹ * a⁻¹⁻¹ = a⁻¹ * (h * a * h⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e, mul_assoc, hc.inv_left.eq, inv_mul_cancel_left]
        exact B₁.inv_mem ha.2⟩ }
  have hVS : V ≤ S := by
    rw [hVgen]
    refine sup_le (sup_le (fun b hb => ⟨hB₁V hb, ?_⟩) (Subgroup.zpowers_le.mpr ⟨hxV, hx⟩))
      (Subgroup.zpowers_le.mpr ⟨hdV, hd⟩)
    rw [hhB b hb, mul_inv_cancel_right, mul_inv_cancel]
    exact B₁.one_mem
  exact fun v hv => (hVS hv).2

end

section

variable {G : Type} [Group G]

theorem hardCase_false [Finite G] {p : ℕ} [Fact p.Prime] {V X N B₁ : Subgroup G} {x d : G}
    (hV : IsElemAbelian p V) (hxV : x ∈ V) (hdV : d ∈ V) (hB₁V : B₁ ≤ V)
    (hB₁X : ∀ b ∈ B₁, ∀ g ∈ X, g * b = b * g)
    (hCB₁ : ∀ v ∈ V, (∀ g ∈ X, g * v = v * g) → v ∈ B₁)
    (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (hXp : ∀ g ∈ X, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (V : Set G))
    (hNX : ∀ n ∈ N, ∀ g ∈ X, n * g * n⁻¹ ∈ X)
    (hNV : N ≤ Subgroup.normalizer (V : Set G)) (hNx : ∀ n ∈ N, n * x = x * n)
    (hxB₁ : x ∉ B₁) (hdB₂ : d ∉ B₁ ⊔ Subgroup.zpowers x)
    (hVgen : V = (B₁ ⊔ Subgroup.zpowers x) ⊔ Subgroup.zpowers d)
    (hB₁inv : ∀ n ∈ N, ∀ b ∈ B₁, n * b * n⁻¹ ∈ B₁)
    (hirr : ∀ S : Subgroup G, S ≤ B₁ → (∀ n ∈ N, ∀ s ∈ S, n * s * n⁻¹ ∈ S) → S = ⊥ ∨ S = B₁)
    (hCN : ∀ v ∈ V, (∀ n ∈ N, n * v = v * n) → v ∈ Subgroup.zpowers x)
    (hNT : ∀ n ∈ N, ∀ v ∈ V, n * v * n⁻¹ * v⁻¹ ∈ B₁)
    (hEnd : ∀ φ : G → G, (∀ h ∈ B₁, φ h ∈ B₁) →
      (∀ h ∈ B₁, ∀ h' ∈ B₁, φ (h * h') = φ h * φ h') →
      (∀ n ∈ N, ∀ h ∈ B₁, φ (n * h * n⁻¹) = n * φ h * n⁻¹) → ∃ c : ℕ, ∀ h ∈ B₁, φ h = h ^ c)
    (hCx : ∀ g ∈ X, g * x = x * g → ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ Subgroup.zpowers x)
    (hcard : p < Nat.card B₁) : False := by
  classical
  have hXV : ∀ g ∈ X, ∀ v ∈ V, g * v * g⁻¹ ∈ V := fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hXN hg) v).mp hv
  have hXV' : ∀ g ∈ X, ∀ v ∈ V, g⁻¹ * v * g ∈ V := fun g hg v hv => by
    simpa using hXV g⁻¹ (X.inv_mem hg) v hv
  have hNV1 : ∀ n ∈ N, ∀ v ∈ V, n * v * n⁻¹ ∈ V := fun n hn v hv =>
    (Subgroup.mem_normalizer_iff.mp (hNV hn) v).mp hv
  have hNV' : ∀ n ∈ N, ∀ v ∈ V, n⁻¹ * v * n ∈ V := fun n hn v hv => by
    simpa using (Subgroup.mem_normalizer_iff.mp (hNV (N.inv_mem hn)) v).mp hv
  have hXB' : ∀ g ∈ X, ∀ b ∈ B₁, g * b * g⁻¹ = b := fun g hg b hb => by
    rw [hB₁X b hb g hg, mul_inv_cancel_right]
  have hXB : ∀ g ∈ X, ∀ b ∈ B₁, g * b * g⁻¹ ∈ B₁ := fun g hg b hb => by
    rw [hXB' g hg b hb]; exact hb
  have hcV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    mul_comm_of_isElemAbelian hV ha hb
  have hxp : x ^ p = 1 := hV.2 x hxV
  have hB₁Z : ∀ b ∈ B₁, b ∈ Subgroup.zpowers x → b = 1 := by
    intro b hb hbZ
    by_contra hb1
    have hz := zpowers_eq_of_mem_of_ne_one hxp hbZ hb1
    have h' : Subgroup.zpowers b ≤ B₁ := Subgroup.zpowers_le.mpr hb
    rw [hz] at h'
    exact hxB₁ (Subgroup.zpowers_le.mp h')
  let P₀ : Subgroup G :=
    { carrier := {g | g ∈ X ∧ ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ B₁}
      mul_mem' := fun {a b} ha hb => ⟨X.mul_mem ha.1 hb.1, triv_mod_mul (hXB a ha.1) ha.2 hb.2⟩
      one_mem' := ⟨X.one_mem, fun v _ => by simp⟩
      inv_mem' := fun {a} ha => ⟨X.inv_mem ha.1, triv_mod_inv (hXV' a ha.1) ha.2⟩ }
  have hP₀ : ∀ g, g ∈ P₀ ↔ g ∈ X ∧ ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ B₁ := fun _ => Iff.rfl
  obtain ⟨g₀, hg₀, n₀, hn₀, hk₀C⟩ := hard_exists_comm hV hxV hCB₁ hXN hXp hNx hxB₁ hCN
  have hk₀P : g₀ * n₀ * g₀⁻¹ * n₀⁻¹ ∈ P₀ := by
    refine (hP₀ _).mpr ⟨?_, ?_⟩
    · have := X.mul_mem hg₀ (hNX n₀ hn₀ g₀⁻¹ (X.inv_mem hg₀))
      simpa [mul_assoc] using this
    · have h1 := triv_mod_conj (hXV' g₀ hg₀) (hXB g₀ hg₀) (hNT n₀ hn₀)
      have h2 := triv_mod_inv (hNV' n₀ hn₀) (hNT n₀ hn₀)
      have hgnB : ∀ b ∈ B₁, g₀ * n₀ * g₀⁻¹ * b * (g₀ * n₀ * g₀⁻¹)⁻¹ ∈ B₁ := by
        intro b hb
        have e : g₀ * n₀ * g₀⁻¹ * b * (g₀ * n₀ * g₀⁻¹)⁻¹ =
            g₀ * (n₀ * (g₀⁻¹ * b * g₀⁻¹⁻¹) * n₀⁻¹) * g₀⁻¹ := by group
        rw [e, hXB' g₀⁻¹ (X.inv_mem hg₀) b hb]
        exact hXB g₀ hg₀ _ (hB₁inv n₀ hn₀ b hb)
      exact triv_mod_mul hgnB h1 h2
  set k₀ := g₀ * n₀ * g₀⁻¹ * n₀⁻¹ with hk₀def
  have hS6 : ∀ g ∈ P₀, g * x = x * g → g ∈ Subgroup.centralizer (V : Set G) := by
    intro g hg hgx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := hB₁Z _ (((hP₀ g).mp hg).2 v hv) (hCx g ((hP₀ g).mp hg).1 hgx v hv)
    calc v * g = (g * v * g⁻¹ * v⁻¹)⁻¹ * g * v := by group
      _ = g * v := by rw [h1, inv_one, one_mul]
  have hθk₀ : k₀ * x * k₀⁻¹ * x⁻¹ ≠ 1 := by
    intro h1
    apply hk₀C
    refine hS6 k₀ hk₀P ?_
    calc k₀ * x = k₀ * x * k₀⁻¹ * x⁻¹ * x * k₀ := by group
      _ = x * k₀ := by rw [h1, one_mul]
  have hfvex : ∀ v ∈ V, ∃ f : P₀ →* G, ∀ g : P₀, f g = (g : G) * v * (g : G)⁻¹ * v⁻¹ :=
    fun v hv => ⟨MonoidHom.mk' (fun g => (g : G) * v * (g : G)⁻¹ * v⁻¹) (fun g h => by
      simp only [Subgroup.coe_mul]
      exact comm_mul_eq (fun b hb => hB₁X b hb g ((hP₀ g).mp g.2).1) (((hP₀ h).mp h.2).2 v hv)
        (hcV _ (hB₁V (((hP₀ g).mp g.2).2 v hv)) _ (hB₁V (((hP₀ h).mp h.2).2 v hv)))),
      fun _ => rfl⟩
  obtain ⟨fx, hfx⟩ := hfvex x hxV
  obtain ⟨fd, hfd⟩ := hfvex d hdV
  have hnxx : ∀ n ∈ N, n * x * n⁻¹ = x := fun n hn => by rw [hNx n hn, mul_inv_cancel_right]
  have hconjP₀ : ∀ n ∈ N, ∀ g ∈ P₀, n * g * n⁻¹ ∈ P₀ := fun n hn g hg =>
    (hP₀ _).mpr ⟨hNX n hn g ((hP₀ g).mp hg).1,
      triv_mod_conj (hNV' n hn) (hB₁inv n hn) ((hP₀ g).mp hg).2⟩
  have hθeq : ∀ n (hn : n ∈ N) (g : P₀),
      n * fx g * n⁻¹ = fx ⟨n * g * n⁻¹, hconjP₀ n hn g g.2⟩ := by
    intro n hn g
    rw [hfx, hfx]
    show n * ((g : G) * x * (g : G)⁻¹ * x⁻¹) * n⁻¹ =
      n * (g : G) * n⁻¹ * x * (n * (g : G) * n⁻¹)⁻¹ * x⁻¹
    calc n * ((g : G) * x * (g : G)⁻¹ * x⁻¹) * n⁻¹
        = n * g * n⁻¹ * (n * x * n⁻¹) * (n * g * n⁻¹)⁻¹ * (n * x * n⁻¹)⁻¹ := by group
      _ = n * (g : G) * n⁻¹ * x * (n * (g : G) * n⁻¹)⁻¹ * x⁻¹ := by rw [hnxx n hn]
  have hθle : fx.range ≤ B₁ := by
    rintro _ ⟨g, rfl⟩
    rw [hfx]
    exact ((hP₀ g).mp g.2).2 x hxV
  have hθinv : ∀ n ∈ N, ∀ s ∈ fx.range, n * s * n⁻¹ ∈ fx.range := by
    rintro n hn _ ⟨g, rfl⟩
    rw [hθeq n hn g]
    exact ⟨_, rfl⟩
  have hθrange : fx.range = B₁ := by
    rcases hirr _ hθle hθinv with h | h
    · exfalso
      apply hθk₀
      have hmem : fx ⟨k₀, hk₀P⟩ ∈ fx.range := ⟨_, rfl⟩
      rw [h, Subgroup.mem_bot, hfx] at hmem
      exact hmem
    · exact h
  have hsurj : ∀ b ∈ B₁, ∃ g : P₀, fx g = b := fun b hb => by
    rw [← hθrange] at hb
    exact hb
  let φ : G → G := fun b => if hb : b ∈ B₁ then fd (Classical.choose (hsurj b hb)) else 1
  have hφ : ∀ g : P₀, φ (fx g) = fd g := by
    intro g
    have hb : fx g ∈ B₁ := hθle ⟨g, rfl⟩
    have hg' := Classical.choose_spec (hsurj _ hb)
    have e : φ (fx g) = fd (Classical.choose (hsurj _ hb)) := dite_eq_left hb
    rw [e]
    set g' := Classical.choose (hsurj _ hb)
    have hker : fx (g'⁻¹ * g) = 1 := by rw [map_mul, map_inv, hg', inv_mul_cancel]
    have hc : ((g'⁻¹ * g : P₀) : G) ∈ Subgroup.centralizer (V : Set G) := by
      refine hS6 _ (g'⁻¹ * g).2 ?_
      rw [hfx] at hker
      calc ((g'⁻¹ * g : P₀) : G) * x
          = ((g'⁻¹ * g : P₀) : G) * x * ((g'⁻¹ * g : P₀) : G)⁻¹ * x⁻¹ * x *
              ((g'⁻¹ * g : P₀) : G) := by group
        _ = x * ((g'⁻¹ * g : P₀) : G) := by rw [hker, one_mul]
    have hfd1 : fd (g'⁻¹ * g) = 1 := by
      rw [hfd, ← Subgroup.mem_centralizer_iff.mp hc d hdV]
      group
    rw [map_mul, map_inv] at hfd1
    exact inv_mul_eq_one.mp hfd1
  have hφB : ∀ b ∈ B₁, φ b ∈ B₁ := by
    intro b hb
    obtain ⟨g, rfl⟩ := hsurj b hb
    rw [hφ, hfd]
    exact ((hP₀ g).mp g.2).2 d hdV
  have hφmul : ∀ b ∈ B₁, ∀ b' ∈ B₁, φ (b * b') = φ b * φ b' := by
    intro b hb b' hb'
    obtain ⟨g, rfl⟩ := hsurj b hb
    obtain ⟨g', rfl⟩ := hsurj b' hb'
    rw [← map_mul, hφ, hφ, hφ, map_mul]
  have hNcomm : ∀ n ∈ N, ∀ g ∈ X, ∀ w ∈ V, g * w * g⁻¹ * w⁻¹ ∈ B₁ →
      n * g * n⁻¹ * w * (n * g * n⁻¹)⁻¹ * w⁻¹ = n * (g * w * g⁻¹ * w⁻¹) * n⁻¹ := by
    intro n hn g hg w hw hgw
    have hb₀ : n⁻¹ * w * n * w⁻¹ ∈ B₁ := by
      have := triv_mod_inv (hNV' n hn) (hNT n hn) w hw
      rwa [inv_inv] at this
    have e1 : n⁻¹ * w * n = (n⁻¹ * w * n * w⁻¹) * w := by group
    have hgb₀ : g * (n⁻¹ * w * n * w⁻¹) * g⁻¹ * (n⁻¹ * w * n * w⁻¹)⁻¹ = 1 := by
      rw [hXB' g hg _ hb₀, mul_inv_cancel]
    calc n * g * n⁻¹ * w * (n * g * n⁻¹)⁻¹ * w⁻¹
        = n * (g * (n⁻¹ * w * n) * g⁻¹ * (n⁻¹ * w * n)⁻¹) * n⁻¹ := by group
      _ = n * (g * ((n⁻¹ * w * n * w⁻¹) * w) * g⁻¹ * ((n⁻¹ * w * n * w⁻¹) * w)⁻¹) * n⁻¹ := by
          rw [← e1]
      _ = n * ((g * (n⁻¹ * w * n * w⁻¹) * g⁻¹ * (n⁻¹ * w * n * w⁻¹)⁻¹) *
            (g * w * g⁻¹ * w⁻¹)) * n⁻¹ := by
          rw [comm_mul_right_eq hV hB₁V (hB₁V hb₀) hgw (hXV g hg _ (hB₁V hb₀))]
      _ = n * (g * w * g⁻¹ * w⁻¹) * n⁻¹ := by rw [hgb₀, one_mul]
  have hφeq : ∀ n ∈ N, ∀ b ∈ B₁, φ (n * b * n⁻¹) = n * φ b * n⁻¹ := by
    intro n hn b hb
    obtain ⟨g, rfl⟩ := hsurj b hb
    rw [hθeq n hn g, hφ, hφ, hfd, hfd]
    exact hNcomm n hn g ((hP₀ g).mp g.2).1 d hdV (((hP₀ g).mp g.2).2 d hdV)
  obtain ⟨c, hc⟩ := hEnd φ hφB hφmul hφeq
  have hxcV : (x ^ c)⁻¹ ∈ V := V.inv_mem (V.pow_mem hxV c)
  have hd'V : d * (x ^ c)⁻¹ ∈ V := V.mul_mem hdV hxcV
  have hP₀d' : ∀ g ∈ P₀, g * (d * (x ^ c)⁻¹) * g⁻¹ * (d * (x ^ c)⁻¹)⁻¹ = 1 := by
    intro g hg
    have hgX := ((hP₀ g).mp hg).1
    have hgT := ((hP₀ g).mp hg).2
    have hcomm : Commute (g * x * g⁻¹ * x⁻¹) x := hcV _ (hB₁V (hgT x hxV)) _ hxV
    have hgxc : g * (x ^ c)⁻¹ * g⁻¹ * ((x ^ c)⁻¹)⁻¹ = (g * x * g⁻¹ * x⁻¹)⁻¹ ^ c := by
      set θ := g * x * g⁻¹ * x⁻¹ with hθdef
      have hθx : g * x * g⁻¹ = θ * x := by rw [hθdef]; group
      calc g * (x ^ c)⁻¹ * g⁻¹ * ((x ^ c)⁻¹)⁻¹ = ((g * x * g⁻¹) ^ c)⁻¹ * x ^ c := by
            rw [conj_pow]; group
        _ = (θ ^ c * x ^ c)⁻¹ * x ^ c := by rw [hθx, hcomm.mul_pow]
        _ = (x ^ c)⁻¹ * ((θ ^ c)⁻¹ * x ^ c) := by group
        _ = (θ ^ c)⁻¹ := by
            rw [((hcomm.pow_pow c c).inv_left).eq, inv_mul_cancel_left]
        _ = θ⁻¹ ^ c := by rw [inv_pow]
    have h1 : g * d * g⁻¹ * d⁻¹ = (g * x * g⁻¹ * x⁻¹) ^ c := by
      have h2 := hφ ⟨g, hg⟩
      rw [hc _ (hθle ⟨⟨g, hg⟩, rfl⟩), hfx, hfd] at h2
      exact h2.symm
    rw [comm_mul_right_eq hV hB₁V hdV (hgT _ hxcV) (hXV g hgX d hdV), hgxc, h1, inv_pow,
      mul_inv_cancel]
  set d' := d * (x ^ c)⁻¹ with hd'def
  have hdd' : d = d' * x ^ c := by rw [hd'def]; group
  have hd'B₂ : d' ∉ B₁ ⊔ Subgroup.zpowers x := by
    intro h
    apply hdB₂
    rw [hdd']
    exact Subgroup.mul_mem _ h
      (le_sup_right (a := B₁) (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) c))
  have hVgen' : V = (B₁ ⊔ Subgroup.zpowers x) ⊔ Subgroup.zpowers d' := by
    apply le_antisymm
    · conv_lhs => rw [hVgen]
      refine sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_)
      rw [hdd']
      exact Subgroup.mul_mem _ (le_sup_right (a := B₁ ⊔ Subgroup.zpowers x)
          (Subgroup.mem_zpowers d'))
        (le_sup_left (a := B₁ ⊔ Subgroup.zpowers x) (b := Subgroup.zpowers d')
          (le_sup_right (a := B₁) (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) c)))
    · exact sup_le (sup_le hB₁V (Subgroup.zpowers_le.mpr hxV)) (Subgroup.zpowers_le.mpr hd'V)
  have hk₀X := ((hP₀ _).mp hk₀P).1
  have hθk₀B : k₀ * x * k₀⁻¹ * x⁻¹ ∈ B₁ := ((hP₀ _).mp hk₀P).2 x hxV
  have hCP₀ : ∀ v ∈ V, k₀ * v * k₀⁻¹ * v⁻¹ = 1 → v ∈ B₁ ⊔ Subgroup.zpowers d' := by
    intro v hv hvk
    rw [hVgen'] at hv
    have hd'comm : ∀ w ∈ B₁ ⊔ Subgroup.zpowers x, d' * w = w * d' := fun w hw =>
      hcV _ hd'V _ (sup_le hB₁V (Subgroup.zpowers_le.mpr hxV) hw)
    obtain ⟨w, hw, j, rfl⟩ := exists_mem_mul_pow_of_mem_sup hd'comm hv
    have hxcomm : ∀ b ∈ B₁, x * b = b * x := fun b hb => hcV _ hxV _ (hB₁V hb)
    obtain ⟨b, hb, i, rfl⟩ := exists_mem_mul_pow_of_mem_sup hxcomm hw
    have hk₀b : k₀ * b * k₀⁻¹ = b := hXB' k₀ hk₀X b hb
    have hk₀d' : k₀ * d' * k₀⁻¹ = d' := by
      have h1 := hP₀d' k₀ hk₀P
      calc k₀ * d' * k₀⁻¹ = k₀ * d' * k₀⁻¹ * d'⁻¹ * d' := by group
        _ = d' := by rw [h1, one_mul]
    have hcθx : Commute (k₀ * x * k₀⁻¹ * x⁻¹) x := hcV _ (hB₁V hθk₀B) _ hxV
    have e : k₀ * (b * x ^ i * d' ^ j) * k₀⁻¹ * (b * x ^ i * d' ^ j)⁻¹ =
        (k₀ * x * k₀⁻¹ * x⁻¹) ^ i := by
      set θ₀ := k₀ * x * k₀⁻¹ * x⁻¹ with hθ₀def
      have hk₀x : k₀ * x * k₀⁻¹ = θ₀ * x := by rw [hθ₀def]; group
      have hθ₀B : θ₀ ∈ B₁ := hθk₀B
      calc k₀ * (b * x ^ i * d' ^ j) * k₀⁻¹ * (b * x ^ i * d' ^ j)⁻¹
          = (k₀ * b * k₀⁻¹) * (k₀ * x * k₀⁻¹) ^ i * (k₀ * d' * k₀⁻¹) ^ j *
              (b * x ^ i * d' ^ j)⁻¹ := by rw [conj_pow, conj_pow]; group
        _ = b * (θ₀ ^ i * x ^ i) * d' ^ j * (b * x ^ i * d' ^ j)⁻¹ := by
            rw [hk₀b, hk₀d', hk₀x, hcθx.mul_pow]
        _ = b * θ₀ ^ i * b⁻¹ := by group
        _ = θ₀ ^ i := by
            rw [hcV b (hB₁V hb) _ (V.pow_mem (hB₁V hθ₀B) i), mul_inv_cancel_right]
    rw [e] at hvk
    have hord : orderOf (k₀ * x * k₀⁻¹ * x⁻¹) = p := orderOf_eq_prime (hV.2 _ (hB₁V hθk₀B)) hθk₀
    obtain ⟨t, rfl⟩ : p ∣ i := hord ▸ orderOf_dvd_of_pow_eq_one hvk
    rw [pow_mul, hxp, one_pow, mul_one]
    exact Subgroup.mul_mem _ (le_sup_left (a := B₁) hb)
      (le_sup_right (a := B₁) (Subgroup.pow_mem _ (Subgroup.mem_zpowers d') j))
  have hXk₀ : ∀ g ∈ X, g⁻¹ * k₀ * g ∈ P₀ := by
    intro g hg
    refine (hP₀ _).mpr ⟨X.mul_mem (X.mul_mem (X.inv_mem hg) hk₀X) hg, ?_⟩
    have h1 := triv_mod_conj (g := g⁻¹) (n := k₀) (fun v hv => by simpa using hXV g hg v hv)
      (hXB g⁻¹ (X.inv_mem hg)) ((hP₀ _).mp hk₀P).2
    simpa only [inv_inv] using h1
  have hXd' : ∀ g ∈ X, g * d' * g⁻¹ ∈ B₁ ⊔ Subgroup.zpowers d' := by
    intro g hg
    apply hCP₀ _ (hXV g hg d' hd'V)
    have h1 := hP₀d' _ (hXk₀ g hg)
    calc k₀ * (g * d' * g⁻¹) * k₀⁻¹ * (g * d' * g⁻¹)⁻¹
        = g * ((g⁻¹ * k₀ * g) * d' * (g⁻¹ * k₀ * g)⁻¹ * d'⁻¹) * g⁻¹ := by group
      _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
  have hV'V : B₁ ⊔ Subgroup.zpowers d' ≤ V := sup_le hB₁V (Subgroup.zpowers_le.mpr hd'V)
  have hXH : ∀ g ∈ X, ∀ h ∈ B₁ ⊔ Subgroup.zpowers d',
      g * h * g⁻¹ ∈ B₁ ⊔ Subgroup.zpowers d' := by
    intro g hg
    have hle : B₁ ⊔ Subgroup.zpowers d' ≤
        (B₁ ⊔ Subgroup.zpowers d').comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun b hb => ?_) (Subgroup.zpowers_le.mpr ?_)
      · show g * b * g⁻¹ ∈ B₁ ⊔ Subgroup.zpowers d'
        rw [hXB' g hg b hb]
        exact le_sup_left (a := B₁) hb
      · exact hXd' g hg
    intro h hh
    exact hle hh
  have hXd'B : ∀ g ∈ X, g * d' * g⁻¹ * d'⁻¹ ∈ B₁ := by
    intro g hg
    have hgV' : g ∈ Subgroup.normalizer ((B₁ ⊔ Subgroup.zpowers d' : Subgroup G) : Set G) := by
      apply mem_normalizer_of_forall_conj_mem
      intro w hw
      have := hXH g⁻¹ (X.inv_mem hg) w hw
      rwa [inv_inv] at this
    obtain ⟨k, hk⟩ := hXp g hg
    exact conj_mul_inv_mem_of_pow_centralizes (isElemAbelian_of_le hV hV'V) le_sup_left
      (le_sup_right (a := B₁) (Subgroup.mem_zpowers d')) rfl hgV'
      (fun b hb => hB₁X b hb g hg) (Subgroup.mem_centralizer_iff.mp hk d' hd'V).symm
  obtain ⟨fd', hfd'⟩ : ∃ f : X →* G, ∀ g : X, f g = (g : G) * d' * (g : G)⁻¹ * d'⁻¹ :=
    ⟨MonoidHom.mk' (fun g => (g : G) * d' * (g : G)⁻¹ * d'⁻¹) (fun g h => by
      simp only [Subgroup.coe_mul]
      exact comm_mul_eq (fun b hb => hB₁X b hb g g.2) (hXd'B h h.2)
        (hcV _ (hB₁V (hXd'B g g.2)) _ (hB₁V (hXd'B h h.2)))), fun _ => rfl⟩
  have hI'B : fd'.range ≤ B₁ := by
    rintro _ ⟨g, rfl⟩
    rw [hfd']
    exact hXd'B g g.2
  have hI'inv : ∀ n ∈ N, ∀ s ∈ fd'.range, n * s * n⁻¹ ∈ fd'.range := by
    rintro n hn _ ⟨g, rfl⟩
    refine ⟨⟨n * g * n⁻¹, hNX n hn g g.2⟩, ?_⟩
    rw [hfd', hfd']
    exact hNcomm n hn g g.2 d' hd'V (hXd'B g g.2)
  have hVH : V = (B₁ ⊔ Subgroup.zpowers d') ⊔ Subgroup.zpowers x := by
    rw [hVgen', sup_right_comm]
  have hXx : ∀ g ∈ X, ∃ b ∈ B₁, ∃ j : ℕ, g * x * g⁻¹ * x⁻¹ = b * d' ^ j := by
    intro g hg
    obtain ⟨k, hk⟩ := hXp g hg
    have h1 := conj_mul_inv_mem_of_pow_normalizes hV hV'V hxV hVH (hXN hg) (hXH g hg)
      (Subgroup.mem_centralizer_iff.mp hk x hxV).symm
    exact exists_mem_mul_pow_of_mem_sup (fun b hb => hcV _ hd'V _ (hB₁V hb)) h1
  have hkey : ∀ (g : G) (hg : g ∈ X) (g' : G) (hg' : g' ∈ X), ∀ b ∈ B₁, ∀ b' ∈ B₁, ∀ j : ℕ,
      g * x * g⁻¹ * x⁻¹ = b * d' ^ j → g' * x * g'⁻¹ * x⁻¹ = b' * d' ^ j →
      fd' ⟨g, hg⟩ = fd' ⟨g', hg'⟩ := by
    intro g hg g' hg' b hb b' hb' j hj hj'
    have hh : g'⁻¹ * g ∈ X := X.mul_mem (X.inv_mem hg') hg
    have hhx : (g'⁻¹ * g) * x * (g'⁻¹ * g)⁻¹ * x⁻¹ ∈ B₁ := by
      have e : (g'⁻¹ * g) * x * (g'⁻¹ * g)⁻¹ * x⁻¹ =
          g'⁻¹ * ((g * x * g⁻¹ * x⁻¹) * (g' * x * g'⁻¹ * x⁻¹)⁻¹) * g'⁻¹⁻¹ := by group
      rw [e, hj, hj']
      have e2 : b * d' ^ j * (b' * d' ^ j)⁻¹ = b * b'⁻¹ := by group
      rw [e2]
      exact hXB g'⁻¹ (X.inv_mem hg') _ (B₁.mul_mem hb (B₁.inv_mem hb'))
    have hT := triv_mod_of_gen hV hB₁V hxV hd'V hVgen' (hXV _ hh) (fun b hb => hB₁X b hb _ hh)
      hhx (hXd'B _ hh)
    have h1 := hP₀d' _ ((hP₀ _).mpr ⟨hh, hT⟩)
    have h2 : fd' ((⟨g', hg'⟩ : X)⁻¹ * ⟨g, hg⟩) = 1 := by
      rw [hfd']
      exact h1
    rw [map_mul, map_inv] at h2
    exact (inv_mul_eq_one.mp h2).symm
  have hd'p : d' ^ p = 1 := hV.2 _ hd'V
  let F : ZMod p → fd'.range := fun c' =>
    if h : ∃ g : X, ∃ b ∈ B₁, (g : G) * x * (g : G)⁻¹ * x⁻¹ = b * d' ^ c'.val then
      ⟨fd' (Classical.choose h), ⟨_, rfl⟩⟩ else 1
  have hF : Function.Surjective F := by
    rintro ⟨_, g, rfl⟩
    obtain ⟨b, hb, j, hj⟩ := hXx g g.2
    have hjv : d' ^ j = d' ^ ((j : ZMod p).val) := by
      rw [ZMod.val_natCast, ← pow_eq_pow_mod_of_pow_eq_one hd'p]
    have hj2 : (g : G) * x * (g : G)⁻¹ * x⁻¹ = b * d' ^ ((j : ZMod p).val) := by
      rw [← hjv]; exact hj
    have hex : ∃ g : X, ∃ b ∈ B₁, (g : G) * x * (g : G)⁻¹ * x⁻¹ = b * d' ^ ((j : ZMod p).val) :=
      ⟨g, b, hb, hj2⟩
    refine ⟨(j : ZMod p), ?_⟩
    have e : F (j : ZMod p) = ⟨fd' (Classical.choose hex), ⟨_, rfl⟩⟩ := dite_eq_left hex
    rw [e]
    apply Subtype.ext
    obtain ⟨b'', hb'', hj''⟩ := Classical.choose_spec hex
    exact hkey _ (Classical.choose hex).2 _ g.2 _ hb'' _ hb _ hj'' hj2
  have hcardI : Nat.card fd'.range ≤ p := by
    have := Nat.card_le_card_of_surjective F hF
    rwa [Nat.card_zmod] at this
  rcases hirr fd'.range hI'B hI'inv with h | h
  · apply hd'B₂
    refine le_sup_left (a := B₁) (hCB₁ d' hd'V (fun g hg => ?_))
    have hmem : fd' ⟨g, hg⟩ ∈ fd'.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, hfd'] at hmem
    calc g * d' = g * d' * g⁻¹ * d'⁻¹ * d' * g := by group
      _ = d' * g := by rw [hmem, one_mul]
  · rw [h] at hcardI
    omega

end

section Inputs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGTableBAction (Bs : Subgroup G) (x : G) (L B₂ : Subgroup G) : Prop :=
  (∀ v ∈ Bs, (∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), n * v = v * n) →
      v ∈ Subgroup.zpowers x) ∧
    ∀ H : Subgroup G, H ≤ B₂ →
      (∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ h ∈ H, n * h * n⁻¹ ∈ H) →
      H ⊔ Subgroup.zpowers x = B₂ → H ⊓ Subgroup.zpowers x = ⊥ →
      (∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ v ∈ Bs, n * v * n⁻¹ * v⁻¹ ∈ H) ∧
      ∀ φ : G → G, (∀ h ∈ H, φ h ∈ H) → (∀ h ∈ H, ∀ h' ∈ H, φ (h * h') = φ h * φ h') →
        (∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ h ∈ H, φ (n * h * n⁻¹) = n * φ h * n⁻¹) →
        ∃ c : ℕ, ∀ h ∈ H, φ h = h ^ c

end Inputs

@[expose] def GGTableBActionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J B₂ : Subgroup G),
    GGConfig p B Bs x L D J → GGTableBModule p Bs x L B₂ → GGTableBAction Bs x L B₂

theorem ggL43HardInput_of_tableB (hTB : GGTableBCxInput) (hTBA : GGTableBActionInput) :
    GGL43HardInput := by
  intro G _ _ p B Bs x L D J X B₂ hFC hM hxB₁ hB₂eq hB₂ne
  obtain ⟨hcfg, -, hXN, hCX, hXn, hXp, hXC⟩ := id hFC
  have : Fact p.Prime := ⟨hcfg.1.2.2.2.2.2.1.1⟩
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hxp : x ^ p = 1 := hBs.2 x hxBs
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.1.2.2.2.2.2.2.1.2.2.2.1.1
  obtain ⟨hCN, hH⟩ := hTBA G p B Bs x L D J B₂ hcfg hM
  obtain ⟨hxB₂, hB₂V, hcardB₂, hB₂inv, hirr₂, -⟩ := hM
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hcV : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    mul_comm_of_isElemAbelian hBs ha hb
  have hconj : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, n * g * n⁻¹ ∈ X := by
    intro n hn g hg
    have := hXn.conj_mem ⟨g, hXN hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨n, hn⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hnx : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), n * x = x * n := fun n hn =>
    (Subgroup.mem_centralizer_iff.mp (hLx hn.1) x rfl).symm
  have hB₁inv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ c ∈ B₁, n * c * n⁻¹ ∈ B₁ := by
    intro n hn c hc
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hn.2 c).mp hc.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hg' : n⁻¹ * g * n⁻¹⁻¹ ∈ X := hconj _ (Subgroup.inv_mem _ hn.2) g hg
    have hcg := Subgroup.mem_centralizer_iff.mp hc.2 _ hg'
    rw [inv_inv] at hcg
    calc g * (n * c * n⁻¹) = n * ((n⁻¹ * g * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * g * n)) * n⁻¹ := by rw [hcg]
      _ = n * c * n⁻¹ * g := by group
  have hB₁Z1 : ∀ b ∈ B₁, b ∈ Subgroup.zpowers x → b = 1 := by
    intro b hb hbZ
    by_contra hb1
    have hz := zpowers_eq_of_mem_of_ne_one hxp hbZ hb1
    have h' : Subgroup.zpowers b ≤ B₁ := Subgroup.zpowers_le.mpr hb
    rw [hz] at h'
    exact hxB₁ (Subgroup.zpowers_le.mp h')
  have hB₁Z : B₁ ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    exact (Subgroup.mem_bot).mpr (hB₁Z1 b hb.1 hb.2)
  have hB₁B₂ : B₁ ≤ B₂ := hB₂eq ▸ le_sup_left
  obtain ⟨hNT, hEnd⟩ := hH B₁ hB₁B₂ hB₁inv hB₂eq hB₁Z
  obtain ⟨d, hdBs, hdB₂⟩ : ∃ d ∈ Bs, d ∉ B₂ := by
    by_contra h
    push Not at h
    exact hB₂ne (le_antisymm hB₂V h)
  have hBsp := isPGroup_of_isElemAbelian hBs
  have hVgen : Bs = (B₁ ⊔ Subgroup.zpowers x) ⊔ Subgroup.zpowers d := by
    rw [hB₂eq]
    refine (eq_of_lt_of_card_le_mul hBsp (lt_of_le_of_ne le_sup_left ?_)
      (sup_le hB₂V (Subgroup.zpowers_le.mpr hdBs)) hcardB₂).symm
    intro h
    apply hdB₂
    rw [h]
    exact le_sup_right (a := B₂) (Subgroup.mem_zpowers d)
  have hZinv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ z ∈ Subgroup.zpowers x,
      n * z * n⁻¹ ∈ Subgroup.zpowers x := by
    intro n hn z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, hnx n hn, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
  have hirr : ∀ S : Subgroup G, S ≤ B₁ →
      (∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ S, n * s * n⁻¹ ∈ S) →
      S = ⊥ ∨ S = B₁ := by
    intro S hSB hSinv
    have hZB₂ : Subgroup.zpowers x ≤ B₂ := Subgroup.zpowers_le.mpr hxB₂
    rcases hirr₂ (S ⊔ Subgroup.zpowers x) le_sup_right (sup_le (hSB.trans hB₁B₂) hZB₂)
      (fun n hn => conj_mem_sup_of_conj_mem (hSinv n hn) (hZinv n hn)) with h | h
    · left
      rw [eq_bot_iff]
      intro s hs
      have hsZ : s ∈ Subgroup.zpowers x := by rw [← h]; exact le_sup_left (a := S) hs
      exact (Subgroup.mem_bot).mpr (hB₁Z1 s (hSB hs) hsZ)
    · right
      refine le_antisymm hSB (fun b hb => ?_)
      have hbS : b ∈ S ⊔ Subgroup.zpowers x := by rw [h, ← hB₂eq]; exact le_sup_left (a := B₁) hb
      have hxS : ∀ s ∈ S, x * s = s * x := fun s hs => hcV _ hxBs _ (hSB hs).1
      obtain ⟨s, hs, i, rfl⟩ := exists_mem_mul_pow_of_mem_sup hxS hbS
      have hxi : x ^ i ∈ B₁ := by
        have := B₁.mul_mem (B₁.inv_mem (hSB hs)) hb
        simpa using this
      rw [hB₁Z1 _ hxi (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i), mul_one]
      exact hs
  have hCx : ∀ g ∈ X, g * x = x * g → ∀ v ∈ Bs, g * v * g⁻¹ * v⁻¹ ∈ Subgroup.zpowers x := by
    intro g hg hgx v hv
    have hCxle : Subgroup.centralizer (Bs : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxBs)
    have hgC : g ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro y rfl
      exact hgx.symm
    refine hTB G p B Bs x L D J hcfg (X ⊓ Subgroup.centralizer ({x} : Set G)) inf_le_right
      (inf_le_left.trans hXN) (le_inf hCX hCxle)
      (fun n hn h hh => Subgroup.mem_inf.mpr ⟨hconj n hn.1 h hh.1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hn.2 hh.2) (Subgroup.inv_mem _ hn.2)⟩)
      (fun h hh => hXp h hh.1) g (Subgroup.mem_inf.mpr ⟨hg, hgC⟩) v hv
  have hcard : p < Nat.card B₁ := by
    have hp := (Fact.out : p.Prime)
    have hB4 : p ^ 4 ≤ Nat.card Bs := by
      have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.2.1.1.2.1
      have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
      calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4
        _ = Nat.card B := hBc.symm
        _ ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1
    have hZcard : Nat.card (Subgroup.zpowers x) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
    have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (B₁ : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun b hb => hcV _ hb.1 _ hxBs)
    have hB₂card : Nat.card B₂ ≤ Nat.card B₁ * p := by
      have h1 := Set.natCard_mul_le (s := (B₁ : Set G)) (t := (Subgroup.zpowers x : Set G))
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left B₁ _ hxN, hB₂eq] at h1
      rw [← hZcard]
      exact h1
    have h2 : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card B₁ := by
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ Nat.card Bs := hB4
        _ ≤ p * Nat.card B₂ := hcardB₂
        _ ≤ p * (Nat.card B₁ * p) := Nat.mul_le_mul_left p hB₂card
        _ = p ^ 2 * Nat.card B₁ := by ring
    have h3 : p ^ 2 ≤ Nat.card B₁ := Nat.le_of_mul_le_mul_left h2 (pow_pos hp.pos 2)
    have h4 : p < p ^ 2 := by nlinarith [hp.two_le]
    omega
  exact hardCase_false (V := Bs) (X := X) (N := L ⊓ Subgroup.normalizer (Bs : Set G)) (B₁ := B₁)
    (x := x) (d := d) hBs hxBs hdBs inf_le_left
    (fun b hb g hg => Subgroup.mem_centralizer_iff.mp hb.2 g hg)
    (fun v hv hvX => ⟨hv, Subgroup.mem_centralizer_iff.mpr hvX⟩)
    hXN hXp (fun n hn g hg => hconj n hn.2 g hg) inf_le_right hnx hxB₁
    (by rw [hB₂eq]; exact hdB₂) hVgen hB₁inv hirr hCN hNT hEnd hCx hcard

end CFSG.StandardType

end
