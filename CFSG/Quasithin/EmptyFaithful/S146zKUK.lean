module

public import CFSG.Quasithin.EmptyFaithful.S146zKAlg
public import CFSG.Quasithin.EmptyFaithful.S146F17
public import CFSG.Quasithin.EmptyFaithful.S146P8
public import CFSG.Quasithin.EmptyFaithful.S14612DC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section UKz

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem conjClosure_eq_sup_uK_z (T M H : Subgroup G) :
    conjClosure (VZ T M) H = VZ T M ⊔ uK T M H := by
  apply le_antisymm
  · refine conjClosure_le fun h hh x hx => ?_
    have hxU : x ∈ conjClosure (VZ T M) H := le_conjClosure _ _ hx
    have hc : x * h * x⁻¹ * h⁻¹ ∈ uK T M H := Subgroup.commutator_mem_commutator hxU hh
    have e : h * x * h⁻¹ = (x * h * x⁻¹ * h⁻¹)⁻¹ * x := by group
    rw [e]
    exact (VZ T M ⊔ uK T M H).mul_mem ((VZ T M ⊔ uK T M H).inv_mem (Subgroup.mem_sup_right hc))
      (Subgroup.mem_sup_left hx)
  · exact sup_le (le_conjClosure _ _)
      (S145.commutator_le_of_le_normalizer (le_normalizer_conjClosure _ _))

theorem IsDec12.commutator_uK_ne_bot (S : Setting146 G T M) (h5 : Stage1461Five)
    (h16 : Stage14616) (h4 : Stage1463Four) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) (hp3 : p = 3) (hOF : IsOFourPlusOn T M H)
    (h : IsDec12 T M H p H₀ H₁ H₂ t)
    (hMod : ∀ u ∈ uHi T M H H₁, u ∉ quasithinOmegaOneCenter T →
      ∃ x ∈ oTwoUpper H₁, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T)
    (hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T)) {g : G}
    (hnc : ¬ ⁅uHi T M H H₁, conjSub g⁻¹ (conjClosure (VZ T M) H)⁆ ≤ quasithinOmegaOneCenter T)
    (hn : conjSub g⁻¹ (conjClosure (VZ T M) H) ≤
      H ⊓ Subgroup.normalizer (uHi T M H H₁ : Set G))
    (hle : conjClosure (VZ T M) H ≤ conjSub g⁻¹ H) :
    ⁅uK T M H, conjSub g⁻¹ (uK T M H)⁆ ≠ ⊥ := by
  classical
  intro hbad
  have hH : IsHTM T M H := hred.isHTM
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hHC : ∀ y ∈ H, ∀ z ∈ quasithinOmegaOneCenter T, y * z = z * y := by
    intro y hy z hz
    have h1 := hHN hy
    rw [normalizer_eq_centralizer_of_card_eq_two S.card_Z] at h1
    exact (Subgroup.mem_centralizer_iff.mp h1 z hz).symm
  have hUH : conjClosure (VZ T M) H ≤ H :=
    (S.conjClosure_le_pCoreOf hH).trans (pCoreOf_le 2 H)
  have hUZ : ∀ y ∈ conjClosure (VZ T M) H, ∀ z ∈ quasithinOmegaOneCenter T, y * z = z * y :=
    fun y hy z hz => hHC y (hUH hy) z hz
  have hKU : uK T M H ≤ conjClosure (VZ T M) H :=
    S145.commutator_le_of_le_normalizer (le_normalizer_conjClosure _ _)
  have hZK : quasithinOmegaOneCenter T ≤ uK T M H := by
    have h1 := (Z_le_commutator_of_isDecP h5 S hred (h.toIsDecP hred)).1
    exact h1.trans (Subgroup.commutator_mono le_rfl
      (((oTwoUpper_le H₁).trans h.le₁).trans h.le))
  have huHi_le : ∀ Hi : Subgroup G, Hi ≤ H → uHi T M H Hi ≤ uK T M H := fun Hi hHi => by
    unfold uHi
    exact sup_le (Subgroup.commutator_mono le_rfl hHi) hZK
  obtain ⟨u₁, hu₁, -, u₂, hu₂, -, c, hcU, hcH, hV⟩ :=
    input14617V_proved G T M S H PQ p hred hmax hp3 hOF H₀ H₁ H₂ t h
  have hu₁K : u₁ ∈ uK T M H := huHi_le H₁ hH₁H hu₁
  have hu₂K : u₂ ∈ uK T M H := huHi_le H₂ (h.le₂.trans h.le) hu₂
  have hUsup : conjClosure (VZ T M) H ≤ uK T M H ⊔ Subgroup.zpowers c := by
    rw [conjClosure_eq_sup_uK_z T M H]
    refine sup_le ?_ le_sup_left
    rw [hV]
    refine sup_le (hZK.trans le_sup_left) (Subgroup.zpowers_le.mpr ?_)
    exact (uK T M H ⊔ Subgroup.zpowers c).mul_mem
      ((uK T M H ⊔ Subgroup.zpowers c).mul_mem (Subgroup.mem_sup_left hu₁K)
        (Subgroup.mem_sup_left hu₂K)) (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ uHi T M H H₁, ∃ b ∈ conjSub g⁻¹ (conjClosure (VZ T M) H),
      a * b * a⁻¹ * b⁻¹ ∉ quasithinOmegaOneCenter T := by
    by_contra hall
    push Not at hall
    apply hnc
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact hall a ha b hb
  have haU : a ∈ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H ha
  have haK : a ∈ uK T M H := huHi_le H₁ hH₁H ha
  have hbU : g * b * g⁻¹ ∈ conjClosure (VZ T M) H := by
    have := mem_conjSub.mp hb
    simpa using this
  have hκH : g * a * g⁻¹ ∈ H := by
    have := mem_conjSub.mp (hle haU)
    simpa using this
  have hK : ∀ y ∈ uK T M H, (g * a * g⁻¹) * y * (g * a * g⁻¹)⁻¹ * y⁻¹ ∈
      quasithinOmegaOneCenter T := by
    intro y hy
    have hyg : g⁻¹ * y * g ∈ conjSub g⁻¹ (uK T M H) := by
      rw [mem_conjSub]
      have e : (g⁻¹)⁻¹ * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [e]
      exact hy
    have h1 : ⁅a, g⁻¹ * y * g⁆ ∈ ⁅uK T M H, conjSub g⁻¹ (uK T M H)⁆ :=
      Subgroup.commutator_mem_commutator haK hyg
    rw [hbad, Subgroup.mem_bot, commutatorElement_def] at h1
    have e : (g * a * g⁻¹) * y * (g * a * g⁻¹)⁻¹ * y⁻¹ =
        g * (a * (g⁻¹ * y * g) * a⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
    rw [e, h1, mul_one, mul_inv_cancel]
    exact (quasithinOmegaOneCenter T).one_mem
  have hcZ : (g * a * g⁻¹) * c * (g * a * g⁻¹)⁻¹ * c⁻¹ ∈ quasithinOmegaOneCenter T :=
    hcH _ hκH
  have hall := forall_commutator_mem_of_gens hUZ hKU hcU hUsup hK hcZ
  have hz := hall _ hbU
  obtain ⟨u₀, hu₀def⟩ : ∃ u₀ : G, u₀ = a * b * a⁻¹ * b⁻¹ := ⟨_, rfl⟩
  rw [← hu₀def] at hab
  have hz' : g * u₀ * g⁻¹ ∈ quasithinOmegaOneCenter T := by
    have e : g * u₀ * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ := by
      rw [hu₀def]
      group
    rw [e]
    exact hz
  have hu₀H : u₀ ∈ uHi T M H H₁ := by
    have hbN := (hn hb).2
    have h1 := (Subgroup.mem_normalizer_iff.mp hbN a⁻¹).mp ((uHi T M H H₁).inv_mem ha)
    have e : u₀ = a * (b * a⁻¹ * b⁻¹) := by
      rw [hu₀def]
      group
    rw [e]
    exact (uHi T M H H₁).mul_mem ha h1
  have hz1 : g * u₀ * g⁻¹ ≠ 1 := by
    intro h1
    apply hab
    have : u₀ = 1 := by
      have h2 := congrArg (fun x => g⁻¹ * x * g) h1
      simpa [mul_assoc] using h2
    rw [this]
    exact (quasithinOmegaOneCenter T).one_mem
  obtain ⟨y₀, hy₀, hyT⟩ :=
    input14617Orbit_proved G T M S H PQ p hred hp3 hOF H₀ H₁ H₂ t h u₀ hu₀H hab
  exact h.false_of_conj_gen S h5 h16 h4 hred hmax hMod hF hu₀H hab hz' hz1
    (g := g⁻¹) (z := g * u₀ * g⁻¹) (y := y₀) (by group) (h.le₁ hy₀) hyT

theorem IsDec12.exists_conj_uK (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hp3 : p = 3) (hOF : IsOFourPlusOn T M H)
    (h : IsDec12 T M H p H₀ H₁ H₂ t) {g : G}
    (hnc : ¬ ⁅uHi T M H H₁, conjSub g⁻¹ (conjClosure (VZ T M) H)⁆ ≤ quasithinOmegaOneCenter T)
    (hn : conjSub g⁻¹ (conjClosure (VZ T M) H) ≤
      H ⊓ Subgroup.normalizer (uHi T M H H₁ : Set G))
    (hle : conjClosure (VZ T M) H ≤ conjSub g⁻¹ H)
    (hKbad : ⁅uK T M H, conjSub g⁻¹ (uK T M H)⁆ ≠ ⊥) {u : G}
    (hu : u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) (huZ : u ∉ quasithinOmegaOneCenter T)
    (h1 : (tU T u).relIndex (tZero T u) = 2) :
    ∃ g' : G, u ∈ conjSubgroup (uK T M H) g' ∧
      ⁅uK T M H, conjSubgroup (uK T M H) g'⁆ ≠ ⊥ := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have huG : u ∈ mcOf T := by
    rcases hu with hu | hu
    · exact S.mem_mcOf_of_mem_conjClosure hH (uHi_le_conjClosure hH₁H hu)
    · exact S.mem_mcOf_of_mem_conjClosure hH (uHi_le_conjClosure (h.le₂.trans h.le) hu)
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hHK : H ≤ Subgroup.normalizer (uK T M H : Set G) :=
    S145.le_normalizer_commutator hHU Subgroup.le_normalizer
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ uHi T M H H₁, ∃ b ∈ conjSub g⁻¹ (conjClosure (VZ T M) H),
      a * b * a⁻¹ * b⁻¹ ∉ quasithinOmegaOneCenter T := by
    by_contra hall
    push Not at hall
    apply hnc
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact hall a ha b hb
  have haU : a ∈ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H ha
  have hbU : g * b * g⁻¹ ∈ conjClosure (VZ T M) H := by
    have := mem_conjSub.mp hb
    simpa using this
  have hκH : g * a * g⁻¹ ∈ H := by
    have := mem_conjSub.mp (hle haU)
    simpa using this
  obtain ⟨u₀, hu₀def⟩ : ∃ u₀ : G, u₀ = a * b * a⁻¹ * b⁻¹ := ⟨_, rfl⟩
  rw [← hu₀def] at hab
  have hu₀H : u₀ ∈ uHi T M H H₁ := by
    have hbN := (hn hb).2
    have h2 := (Subgroup.mem_normalizer_iff.mp hbN a⁻¹).mp ((uHi T M H H₁).inv_mem ha)
    have e : u₀ = a * (b * a⁻¹ * b⁻¹) := by
      rw [hu₀def]
      group
    rw [e]
    exact (uHi T M H H₁).mul_mem ha h2
  have hu₀K : g * u₀ * g⁻¹ ∈ uK T M H := by
    have h2 : ⁅g * b * g⁻¹, g * a * g⁻¹⁆ ∈ uK T M H :=
      Subgroup.commutator_mem_commutator hbU hκH
    have e : g * u₀ * g⁻¹ = (⁅g * b * g⁻¹, g * a * g⁻¹⁆)⁻¹ := by
      rw [hu₀def, commutatorElement_def]
      group
    rw [e]
    exact (uK T M H).inv_mem h2
  obtain ⟨c, hcH, hc⟩ := input14617Trans_proved G T M S H PQ p hred hp3 hOF H₀ H₁ H₂ t h u₀ u
    (Or.inl hu₀H) hab hu huZ
  obtain ⟨t₁, ht₁T, ht₁⟩ := S.exists_conj_eq_mul_Z huG h1 hc
  have hc₂ : c⁻¹ * t₁ ∈ H := H.mul_mem (H.inv_mem hcH) (hTH ht₁T)
  have hu₀eq : (c⁻¹ * t₁) * u * (c⁻¹ * t₁)⁻¹ = u₀ := by
    have e : (c⁻¹ * t₁) * u * (c⁻¹ * t₁)⁻¹ = c⁻¹ * (t₁ * u * t₁⁻¹) * c := by group
    rw [e, ht₁]
    have e2 : c * u₀ * c⁻¹ = (c * u₀ * c⁻¹ * u⁻¹) * u := by group
    have e3 : u₀ = c⁻¹ * (c * u₀ * c⁻¹) * c := by group
    rw [e3, e2]
    group
  refine ⟨g * (c⁻¹ * t₁), ?_, ?_⟩
  · rw [mem_conjSubgroup_iff]
    have e : g * (c⁻¹ * t₁) * u * (g * (c⁻¹ * t₁))⁻¹ = g * ((c⁻¹ * t₁) * u * (c⁻¹ * t₁)⁻¹) * g⁻¹ := by
      group
    rw [e, hu₀eq]
    exact hu₀K
  · intro hbot
    obtain ⟨k, hk, k', hk', hkk⟩ : ∃ k ∈ uK T M H, ∃ k' ∈ conjSub g⁻¹ (uK T M H),
        k * k' * k⁻¹ * k'⁻¹ ≠ 1 := by
      by_contra hall
      push Not at hall
      apply hKbad
      rw [eq_bot_iff]
      refine Subgroup.commutator_le.mpr fun k hk k' hk' => ?_
      rw [Subgroup.mem_bot, commutatorElement_def]
      exact hall k hk k' hk'
    set c₂ : G := c⁻¹ * t₁ with hc₂def
    have hk₂ : c₂⁻¹ * k * c₂ ∈ uK T M H := by
      have := (Subgroup.mem_normalizer_iff.mp (hHK (H.inv_mem hc₂)) k).mp hk
      simpa using this
    have hk₂' : c₂⁻¹ * k' * c₂ ∈ conjSubgroup (uK T M H) (g * c₂) := by
      rw [mem_conjSubgroup_iff]
      have e : g * c₂ * (c₂⁻¹ * k' * c₂) * (g * c₂)⁻¹ = g * k' * g⁻¹ := by group
      rw [e]
      have := mem_conjSub.mp hk'
      simpa using this
    have h3 : ⁅c₂⁻¹ * k * c₂, c₂⁻¹ * k' * c₂⁆ ∈ ⁅uK T M H, conjSubgroup (uK T M H) (g * c₂)⁆ :=
      Subgroup.commutator_mem_commutator hk₂ hk₂'
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at h3
    apply hkk
    have e : k * k' * k⁻¹ * k'⁻¹ =
        c₂ * ((c₂⁻¹ * k * c₂) * (c₂⁻¹ * k' * c₂) * (c₂⁻¹ * k * c₂)⁻¹ * (c₂⁻¹ * k' * c₂)⁻¹) * c₂⁻¹ := by
      group
    rw [e, h3]
    group

end UKz

theorem input14617UK_of_stages (h5 : Stage1461Five) (h14 : Stage14614) (h16 : Stage14616)
    (h4 : Stage1463Four) (iMod : Input14617Mod) (iF : Input14617Fstar) : Input14617UK := by
  intro G _ _ T M S H PQ p hred hmax hp3 hOF H₀ H₁ H₂ t hdec hcase u hu huZ _ hInv
  have hH : IsHTM T M H := hred.isHTM
  have hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T) :=
    iF G T M S H PQ p hred hmax (stage14614At_of h14 S hred hmax)
  have h1 : (tU T u).relIndex (tZero T u) = 2 := (stage1463_one_proof G T M S H hH u hInv).2.1
  have core : ∀ (H₁' H₂' : Subgroup G) (t' : G) (hdec' : IsDec12 T M H p H₀ H₁' H₂' t'),
      (u ∈ uHi T M H H₁' ∨ u ∈ uHi T M H H₂') → Case13One T M H p H₁' →
        ∃ g' : G, u ∈ conjSubgroup (uK T M H) g' ∧
          ⁅uK T M H, conjSubgroup (uK T M H) g'⁆ ≠ ⊥ := by
    intro H₁' H₂' t' hdec' hu' hc
    obtain ⟨-, -, g, -, hnc, hn, hle⟩ := hc
    have hKbad := hdec'.commutator_uK_ne_bot S h5 h16 h4 hred hmax hp3 hOF
      (iMod G T M S H PQ p hred H₀ H₁' H₂' t' hdec') hF hnc hn hle
    exact hdec'.exists_conj_uK S hred hp3 hOF hnc hn hle hKbad hu' huZ h1
  rcases hcase with hc | hc
  · exact core H₁ H₂ t hdec hu hc
  · exact core H₂ H₁ t⁻¹ hdec.swap hu.symm hc

end CFSG.Quasithin
