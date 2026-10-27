module

public import CFSG.LocalAnalysis.WeakClosure81.W16Inputs
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneRank
public import CFSG.Quasithin.Background.G118Apply

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem mul_mul_mul_comm_of_mem {V : Subgroup G} (hV : IsElemAbelian 2 V) {a b c d : G}
    (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (hd : d ∈ V) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [mul_assoc a b (c * d), ← mul_assoc b c d, B2F.isElemAbelian_comm hV hb hc,
    mul_assoc c b d, ← mul_assoc a c (b * d)]

private theorem inv_eq_self_of_mem {V : Subgroup G} (hV : IsElemAbelian 2 V) {x : G}
    (hx : x ∈ V) : x⁻¹ = x := by
  rw [inv_eq_iff_mul_eq_one]
  simpa [pow_two] using hV.2 x hx

private theorem mul_inv_mul_mul_inv_of_mem {V : Subgroup G} (hV : IsElemAbelian 2 V) {a b c d : G}
    (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (hd : d ∈ V) :
    (a * b) * (c * d)⁻¹ = (a * c⁻¹) * (b * d⁻¹) := by
  have h1 : (a * c⁻¹) * (b * d⁻¹) = (a * b) * (c⁻¹ * d⁻¹) :=
    mul_mul_mul_comm_of_mem hV ha (V.inv_mem hc) hb (V.inv_mem hd)
  have h2 : c⁻¹ * d⁻¹ = (c * d)⁻¹ := by
    rw [mul_inv_rev, B2F.isElemAbelian_comm hV (V.inv_mem hd) (V.inv_mem hc)]
  rw [h1, h2]

private theorem exists_proj_of_isElemAbelian {A B Q V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : A ≤ V) (hB : B ≤ V) (hQ : A ⊔ B = Q) (hinf : A ⊓ B = ⊥) :
    ∃ π : G → G,
      (∀ q ∈ Q, π q ∈ B) ∧
      (∀ a ∈ A, π a = 1) ∧
      (∀ b ∈ B, π b = b) ∧
      (∀ q ∈ Q, q * (π q)⁻¹ ∈ A) ∧
      (∀ q ∈ Q, ∀ q' ∈ Q, π (q * q') = π q * π q') := by
  classical
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x :=
    fun x hx y hy => B2F.isElemAbelian_comm hV hx hy
  have hQV : Q ≤ V := by rw [← hQ]; exact sup_le hA hB
  have hexp : ∀ q ∈ Q, ∃ b ∈ B, q * b⁻¹ ∈ A := by
    intro q hq
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup hA hB hcomm (hQ.symm ▸ hq)
    exact ⟨b, hb, by rw [← hab]; simpa using ha⟩
  let π : G → G := fun q => if hq : q ∈ Q then Classical.choose (hexp q hq) else 1
  have π_mem : ∀ q (hq : q ∈ Q), π q ∈ B := by
    intro q hq
    dsimp only [π]
    rw [dif_pos hq]
    exact (Classical.choose_spec (hexp q hq)).1
  have π_proj : ∀ q ∈ Q, q * (π q)⁻¹ ∈ A := by
    intro q hq
    dsimp only [π]
    rw [dif_pos hq]
    exact (Classical.choose_spec (hexp q hq)).2
  have π_kill : ∀ a ∈ A, π a = 1 := by
    intro a ha
    have haQ : a ∈ Q := hQ ▸ Subgroup.mem_sup_left ha
    have hbA : π a ∈ A := by
      have h1 : (π a)⁻¹ ∈ A := by
        have he : (π a)⁻¹ = a⁻¹ * (a * (π a)⁻¹) := by group
        rw [he]
        exact A.mul_mem (A.inv_mem ha) (π_proj a haQ)
      simpa using A.inv_mem h1
    have hmem : π a ∈ A ⊓ B := ⟨hbA, π_mem a haQ⟩
    rw [hinf] at hmem
    exact Subgroup.mem_bot.1 hmem
  have π_id : ∀ b ∈ B, π b = b := by
    intro b hb
    have hbQ : b ∈ Q := hQ ▸ Subgroup.mem_sup_right hb
    have hmem : b * (π b)⁻¹ ∈ A ⊓ B :=
      ⟨π_proj b hbQ, B.mul_mem hb (B.inv_mem (π_mem b hbQ))⟩
    rw [hinf] at hmem
    exact (mul_inv_eq_one.1 (Subgroup.mem_bot.1 hmem)).symm
  have huniq : ∀ {x b₁ b₂ : G}, b₁ ∈ B → b₂ ∈ B → x * b₁⁻¹ ∈ A → x * b₂⁻¹ ∈ A →
      b₁ = b₂ := by
    intro x b₁ b₂ hb₁ hb₂ h1 h2
    have hmem : b₁ * b₂⁻¹ ∈ A ⊓ B := by
      refine ⟨?_, B.mul_mem hb₁ (B.inv_mem hb₂)⟩
      have he : b₁ * b₂⁻¹ = (x * b₁⁻¹)⁻¹ * (x * b₂⁻¹) := by group
      rw [he]
      exact A.mul_mem (A.inv_mem h1) h2
    rw [hinf] at hmem
    exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 hmem)
  have π_mul : ∀ q ∈ Q, ∀ q' ∈ Q, π (q * q') = π q * π q' := by
    intro q hq q' hq'
    have hQQ : q * q' ∈ Q := Q.mul_mem hq hq'
    have hkey : (q * q') * (π q * π q')⁻¹ ∈ A := by
      rw [mul_inv_mul_mul_inv_of_mem hV (hQV hq) (hQV hq') (hB (π_mem q hq))
        (hB (π_mem q' hq'))]
      exact A.mul_mem (π_proj q hq) (π_proj q' hq')
    exact huniq (π_mem (q * q') hQQ) (B.mul_mem (π_mem q hq) (π_mem q' hq'))
      (π_proj (q * q') hQQ) hkey
  exact ⟨π, π_mem, π_kill, π_id, π_proj, π_mul⟩

private theorem exists_extend_of_isElemAbelian {Q T V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hQ : Q ≤ V) (hT : T ≤ V) (φ : G → G) (hφmem : ∀ q ∈ Q, φ q ∈ T)
    (hφmul : ∀ q ∈ Q, ∀ q' ∈ Q, φ (q * q') = φ q * φ q') :
    ∃ Ψ : G → G, (∀ v ∈ V, Ψ v ∈ T) ∧
      (∀ v ∈ V, ∀ v' ∈ V, Ψ (v * v') = Ψ v * Ψ v') ∧
      (∀ q ∈ Q, Ψ q = φ q) := by
  classical
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x :=
    fun x hx y hy => B2F.isElemAbelian_comm hV hx hy
  obtain ⟨C, hCV, hCQ, hCsup⟩ :=
    CFSG.Quasithin.G11.G118.exists_complement_of_isElemTwo (E := V) (F := Q) hcomm
      (fun a ha => by have := hV.2 a ha; rwa [pow_two] at this) hQ
  have hexp : ∀ v ∈ V, ∃ q ∈ Q, v * q⁻¹ ∈ C := by
    intro v hv
    obtain ⟨c, hc, q, hq, hcq⟩ :=
      exists_mul_of_mem_sup hCV hQ hcomm (hCsup.symm ▸ hv : v ∈ C ⊔ Q)
    exact ⟨q, hq, by rw [← hcq]; simpa using hc⟩
  let Ψ : G → G := fun v => if hv : v ∈ V then φ (Classical.choose (hexp v hv)) else 1
  have huniq : ∀ {v q q' : G}, q ∈ Q → q' ∈ Q → v * q⁻¹ ∈ C → v * q'⁻¹ ∈ C → q = q' := by
    intro v q q' hq hq' h1 h2
    have hmem : q * q'⁻¹ ∈ C ⊓ Q := by
      refine ⟨?_, Q.mul_mem hq (Q.inv_mem hq')⟩
      have he : q * q'⁻¹ = (v * q⁻¹)⁻¹ * (v * q'⁻¹) := by group
      rw [he]
      exact C.mul_mem (C.inv_mem h1) h2
    rw [hCQ] at hmem
    exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 hmem)
  have Ψ_mem : ∀ v ∈ V, Ψ v ∈ T := by
    intro v hv
    dsimp only [Ψ]
    rw [dif_pos hv]
    exact hφmem _ (Classical.choose_spec (hexp v hv)).1
  have Ψ_mul : ∀ v ∈ V, ∀ v' ∈ V, Ψ (v * v') = Ψ v * Ψ v' := by
    intro v hv v' hv'
    have hq : Classical.choose (hexp v hv) ∈ Q := (Classical.choose_spec (hexp v hv)).1
    have hp : v * (Classical.choose (hexp v hv))⁻¹ ∈ C :=
      (Classical.choose_spec (hexp v hv)).2
    have hq' : Classical.choose (hexp v' hv') ∈ Q := (Classical.choose_spec (hexp v' hv')).1
    have hp' : v' * (Classical.choose (hexp v' hv'))⁻¹ ∈ C :=
      (Classical.choose_spec (hexp v' hv')).2
    have hvv' : v * v' ∈ V := V.mul_mem hv hv'
    have hkey : (v * v') *
        (Classical.choose (hexp v hv) * Classical.choose (hexp v' hv'))⁻¹ ∈ C := by
      rw [mul_inv_mul_mul_inv_of_mem hV hv hv' (hQ hq) (hQ hq')]
      exact C.mul_mem hp hp'
    have hchoose : Classical.choose (hexp (v * v') hvv') =
        Classical.choose (hexp v hv) * Classical.choose (hexp v' hv') :=
      huniq (v := v * v') (q := Classical.choose (hexp (v * v') hvv'))
        (q' := Classical.choose (hexp v hv) * Classical.choose (hexp v' hv'))
        (Classical.choose_spec (hexp (v * v') hvv')).1 (Subgroup.mul_mem _ hq hq')
        (Classical.choose_spec (hexp (v * v') hvv')).2 hkey
    dsimp only [Ψ]
    rw [dif_pos hvv', dif_pos hv, dif_pos hv', hchoose, hφmul _ hq _ hq']
  have Ψ_eq : ∀ q ∈ Q, Ψ q = φ q := by
    intro q hq
    have hspec := Classical.choose_spec (hexp q (hQ hq))
    have hone : q * q⁻¹ ∈ C := by simpa using C.one_mem
    have hchoose : Classical.choose (hexp q (hQ hq)) = q := huniq hspec.1 hq hspec.2 hone
    dsimp only [Ψ]
    rw [dif_pos (hQ hq), hchoose]
  exact ⟨Ψ, Ψ_mem, Ψ_mul, Ψ_eq⟩

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem exists_hom_of_complement (c : Cfg1620 M V₀ V U S R H g B) {U' : Subgroup G}
    (hle : U' ≤ U ⊔ V₀) (hinf : U' ⊓ V₀ = ⊥) (hsup : U' ⊔ V₀ = U ⊔ V₀) :
    ∃ Ψ : G → G, (∀ v ∈ V, Ψ v ∈ V₀) ∧ (∀ v ∈ V, ∀ v' ∈ V, Ψ (v * v') = Ψ v * Ψ v') ∧
      (∀ w ∈ V₀, Ψ w = 1) ∧ ∀ x : G, x ∈ U' ↔ ∃ u ∈ U, x = u * Ψ u := by
  classical
  have hV : IsElemAbelian 2 V := c.cex.hyp.h6.elemAbelian
  have hU : U ≤ V := c.cex.le
  have hV₀ : V₀ ≤ V := c.cex.hyp.h6.le
  have hU'V : U' ≤ V := hle.trans (sup_le hU hV₀)
  have hQleV : U ⊔ V₀ ≤ V := sup_le hU hV₀
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x :=
    fun x hx y hy => B2F.isElemAbelian_comm hV hx hy
  obtain ⟨σ, σ_mem, σ_kill, σ_id, σ_proj, σ_mul⟩ :=
    exists_proj_of_isElemAbelian hV hU hV₀ rfl c.cex.inf_eq_bot
  obtain ⟨τ, τ_mem, τ_kill, τ_id, τ_proj, τ_mul⟩ :=
    exists_proj_of_isElemAbelian hV hU'V hV₀ hsup hinf
  let Ψ₀ : G → G := fun y => if y ∈ U ⊔ V₀ then σ y * τ y else 1
  have Ψ₀_mem : ∀ y ∈ U ⊔ V₀, Ψ₀ y ∈ V₀ := by
    intro y hy
    dsimp only [Ψ₀]
    rw [if_pos hy]
    exact V₀.mul_mem (σ_mem y hy) (τ_mem y hy)
  have Ψ₀_mul : ∀ y ∈ U ⊔ V₀, ∀ y' ∈ U ⊔ V₀, Ψ₀ (y * y') = Ψ₀ y * Ψ₀ y' := by
    intro y hy y' hy'
    have hyy' : y * y' ∈ U ⊔ V₀ := (U ⊔ V₀).mul_mem hy hy'
    dsimp only [Ψ₀]
    rw [if_pos hyy', if_pos hy, if_pos hy', σ_mul y hy y' hy', τ_mul y hy y' hy']
    exact mul_mul_mul_comm_of_mem hV (hV₀ (σ_mem y hy)) (hV₀ (σ_mem y' hy'))
      (hV₀ (τ_mem y hy)) (hV₀ (τ_mem y' hy'))
  have Ψ₀_V₀ : ∀ w ∈ V₀, Ψ₀ w = 1 := by
    intro w hw
    have hwQ : w ∈ U ⊔ V₀ := Subgroup.mem_sup_right hw
    dsimp only [Ψ₀]
    rw [if_pos hwQ, σ_id w hw, τ_id w hw]
    have := hV.2 w (hV₀ hw)
    rwa [pow_two] at this
  have Ψ₀_U : ∀ u ∈ U, u * Ψ₀ u ∈ U' := by
    intro u hu
    have huQ : u ∈ U ⊔ V₀ := Subgroup.mem_sup_left hu
    have hτinv : (τ u)⁻¹ = τ u := inv_eq_self_of_mem hV (hV₀ (τ_mem u huQ))
    have h1 : Ψ₀ u = τ u := by
      dsimp only [Ψ₀]
      rw [if_pos huQ, σ_kill u hu]
      group
    rw [h1]
    have := τ_proj u huQ
    rwa [hτinv] at this
  obtain ⟨Ψ, hΨmem, hΨmul, hΨeq⟩ :=
    exists_extend_of_isElemAbelian hV hQleV hV₀ Ψ₀ Ψ₀_mem Ψ₀_mul
  have hΨ1 : ∀ w ∈ V₀, Ψ w = 1 := by
    intro w hw
    rw [hΨeq w (Subgroup.mem_sup_right hw), Ψ₀_V₀ w hw]
  refine ⟨Ψ, hΨmem, hΨmul, hΨ1, ?_⟩
  intro x
  constructor
  · intro hx
    have hxQ : x ∈ U ⊔ V₀ := hle hx
    obtain ⟨u, hu, w, hw, huw⟩ := exists_mul_of_mem_sup hU hV₀ hcomm hxQ
    have huwU' : u * w ∈ U' := by rw [huw]; exact hx
    have huU' : u * Ψ u ∈ U' := by
      rw [hΨeq u (Subgroup.mem_sup_left hu)]
      exact Ψ₀_U u hu
    have hprod : w⁻¹ * Ψ u ∈ V₀ :=
      V₀.mul_mem (V₀.inv_mem hw) (hΨmem u (hU hu))
    have hprodU' : w⁻¹ * Ψ u ∈ U' := by
      have he : w⁻¹ * Ψ u = (u * w)⁻¹ * (u * Ψ u) := by group
      rw [he]
      exact U'.mul_mem (U'.inv_mem huwU') huU'
    have h1 : w⁻¹ * Ψ u = 1 := by
      have hmem : w⁻¹ * Ψ u ∈ U' ⊓ V₀ := ⟨hprodU', hprod⟩
      rw [hinf] at hmem
      exact Subgroup.mem_bot.1 hmem
    have hΨu : Ψ u = w := by
      calc Ψ u = w * (w⁻¹ * Ψ u) := by group
        _ = w * 1 := by rw [h1]
        _ = w := by group
    exact ⟨u, hu, by rw [← huw, hΨu]⟩
  · rintro ⟨u, hu, rfl⟩
    rw [hΨeq u (Subgroup.mem_sup_left hu)]
    exact Ψ₀_U u hu

theorem exists_mem_cTilde_of_hom (c : Cfg1620 M V₀ V U S R H g B)
    (hn : E3.mQuot V (U ⊔ V₀) = 1)
    (hA : ∀ m ∈ M, ∀ w ∈ V₀, ∃ x ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G),
      (∀ v ∈ V, m * v * m⁻¹ ∈ U ⊔ V₀ → x * v * x⁻¹ * v⁻¹ = 1) ∧
      (∀ v ∈ V, m * v * m⁻¹ ∉ U ⊔ V₀ → x * v * x⁻¹ * v⁻¹ = w))
    (hirr : ∀ v ∈ V, (∀ m ∈ M, m * v * m⁻¹ ∈ U ⊔ V₀) → v ∈ V₀) {Ψ : G → G}
    (hΨV₀ : ∀ v ∈ V, Ψ v ∈ V₀) (hΨmul : ∀ v ∈ V, ∀ v' ∈ V, Ψ (v * v') = Ψ v * Ψ v')
    (hΨ1 : ∀ w ∈ V₀, Ψ w = 1) :
    ∃ a ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G), ∀ v ∈ V, a * v * a⁻¹ * v⁻¹ = Ψ v := by
  classical
  have hV : IsElemAbelian 2 V := c.cex.hyp.h6.elemAbelian
  have hV₀ : V₀ ≤ V := c.cex.hyp.h6.le
  have hQleV : U ⊔ V₀ ≤ V := sup_le c.cex.le hV₀
  have hMnormV : M ≤ Subgroup.normalizer (V : Set G) := c.cex.hyp.h6.normalizer_eq ▸ le_rfl
  have hMnormV₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := c.cex.hyp.h6.le_normalizer₀
  let 𝒬 : Set (Subgroup G) := {Q' | ∃ m ∈ M, Q' = conjSubgroup (U ⊔ V₀) m}
  have h𝒬 : ∀ Q' ∈ 𝒬, V₀ ≤ Q' ∧ Q' ≤ V ∧ Q'.relIndex V = 2 := by
    intro Q' hQ'
    obtain ⟨m, hm, rfl⟩ := hQ'
    have hconjV : conjSubgroup V m = V := by
      rw [conjSubgroup_eq_iff_mem_normalizer]
      exact hMnormV hm
    have hconjV₀ : conjSubgroup V₀ m = V₀ := by
      rw [conjSubgroup_eq_iff_mem_normalizer]
      exact hMnormV₀ hm
    refine ⟨?_, ?_, ?_⟩
    · have h := E3.conjSubgroup_mono_left m (le_sup_right : V₀ ≤ U ⊔ V₀)
      rwa [hconjV₀] at h
    · have h := E3.conjSubgroup_mono_left m (hQleV : U ⊔ V₀ ≤ V)
      rwa [hconjV] at h
    · have hrel := E3.relIndex_conjSubgroup (U ⊔ V₀) V m
      rw [hconjV] at hrel
      rw [hrel, E3.relIndex_eq_two_pow c.cex.hyp.isPGroup, hn]
      simp
  have hsep : ∀ v ∈ V, (∀ Q' ∈ 𝒬, v ∈ Q') → v ∈ V₀ := by
    intro v hv h
    apply hirr v hv
    intro m hm
    have hmem := h (conjSubgroup (U ⊔ V₀) m) ⟨m, hm, rfl⟩
    rwa [mem_conjSubgroup_iff] at hmem
  obtain ⟨l, hl_mem, hl_val⟩ :=
    NOne.exists_list_prod_rankOne hV hV₀ 𝒬 h𝒬 hsep hΨV₀ hΨmul hΨ1
  have hind : ∀ l : List (Subgroup G × G), (∀ p ∈ l, p.1 ∈ 𝒬 ∧ p.2 ∈ V₀) →
      ∃ a ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G),
        ∀ v ∈ V, a * v * a⁻¹ * v⁻¹ =
          (l.map fun p => NOne.rankOneMap p.1 p.2 v).prod := by
    intro l
    induction l with
    | nil =>
      intro _
      exact ⟨1, Subgroup.one_mem _, fun v hv => by simp⟩
    | cons p l ih =>
      intro hl
      have hp : p.1 ∈ 𝒬 ∧ p.2 ∈ V₀ := hl p (by rw [List.mem_cons]; exact Or.inl rfl)
      have hl' : ∀ q ∈ l, q.1 ∈ 𝒬 ∧ q.2 ∈ V₀ :=
        fun q hq => hl q (by rw [List.mem_cons]; exact Or.inr hq)
      obtain ⟨a', ha', hprod'⟩ := ih hl'
      obtain ⟨m, hm, hQ'⟩ := hp.1
      obtain ⟨x, hx, hx1, hxw⟩ := hA m hm p.2 hp.2
      have hxA : x ∈ F11.CTilde M V₀ V := (Subgroup.mem_inf.1 hx).1
      have hxV₀ : x ∈ centralizer (V₀ : Set G) := (Subgroup.mem_inf.1 hx).2
      have ha'C : a' ∈ F11.CTilde M V₀ V := (Subgroup.mem_inf.1 ha').1
      have ha'V₀ : a' ∈ centralizer (V₀ : Set G) := (Subgroup.mem_inf.1 ha').2
      refine ⟨x * a', Subgroup.mul_mem _ hx ha', ?_⟩
      intro v hv
      have hxv : x * v * x⁻¹ * v⁻¹ ∈ V₀ := (FourteenTwo.mem_cTilde_iff_comm.1 hxA).2.2 v hv
      have ha'v : a' * v * a'⁻¹ * v⁻¹ ∈ V₀ :=
        (FourteenTwo.mem_cTilde_iff_comm.1 ha'C).2.2 v hv
      have hrank : x * v * x⁻¹ * v⁻¹ = NOne.rankOneMap p.1 p.2 v := by
        by_cases hvQ : v ∈ p.1
        · have hmv : m * v * m⁻¹ ∈ U ⊔ V₀ := by
            have h := hvQ
            rw [hQ', mem_conjSubgroup_iff] at h
            exact h
          rw [hx1 v hv hmv, NOne.rankOneMap_of_mem hvQ]
        · have hmv : m * v * m⁻¹ ∉ U ⊔ V₀ := fun hh =>
            hvQ (by rw [hQ', mem_conjSubgroup_iff]; exact hh)
          rw [hxw v hv hmv, NOne.rankOneMap_of_not_mem hvQ]
      have hxφ : x * (a' * v * a'⁻¹ * v⁻¹) * x⁻¹ = a' * v * a'⁻¹ * v⁻¹ := by
        have hy := (Subgroup.mem_centralizer_iff.1 hxV₀) _ ha'v
        rw [← hy]
        group
      have hcomb : (x * a') * v * (x * a')⁻¹ * v⁻¹ =
          (x * v * x⁻¹ * v⁻¹) * (a' * v * a'⁻¹ * v⁻¹) := by
        calc (x * a') * v * (x * a')⁻¹ * v⁻¹
            = x * (a' * v * a'⁻¹) * x⁻¹ * v⁻¹ := by group
          _ = x * ((a' * v * a'⁻¹ * v⁻¹) * v) * x⁻¹ * v⁻¹ := by group
          _ = (x * (a' * v * a'⁻¹ * v⁻¹) * x⁻¹) * (x * v * x⁻¹) * v⁻¹ := by group
          _ = (a' * v * a'⁻¹ * v⁻¹) * (x * v * x⁻¹) * v⁻¹ := by rw [hxφ]
          _ = (a' * v * a'⁻¹ * v⁻¹) * (x * v * x⁻¹ * v⁻¹) := by group
          _ = (x * v * x⁻¹ * v⁻¹) * (a' * v * a'⁻¹ * v⁻¹) :=
                (B2F.isElemAbelian_comm hV (hV₀ hxv) (hV₀ ha'v)).symm
      rw [List.map_cons, List.prod_cons, hcomb, hrank, hprod' v hv]
  obtain ⟨a, ha, haval⟩ := hind l hl_mem
  exact ⟨a, ha, fun v hv => by rw [haval v hv, hl_val v hv]⟩

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
