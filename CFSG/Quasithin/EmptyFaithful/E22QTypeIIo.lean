module

public import CFSG.Quasithin.EmptyFaithful.E22QWr
public import CFSG.Quasithin.EmptyFaithful.E22QTorus
import CFSG.Quasithin.EmptyFaithful.E22PTor

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b CFSG.Quasithin.E22L2
open scoped commutatorElement

section Outer

variable {G : Type} [Group G] {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ : G}

theorem typeIIo_cent_eq_one (h : Wr p T M J₁ J₂ z₁) {u : G} (h₁ : ∀ g ∈ J₁, g * u = u * g)
    (h₂ : ∀ g ∈ J₂, g * u = u * g) : u = 1 := by
  have hu : u ∈ Subgroup.centralizer ((J₁ ⊔ J₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hle : J₁ ⊔ J₂ ≤ Subgroup.centralizer ({u} : Set G) :=
      sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (h₁ x hx))
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (h₂ x hx))
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  rw [h.cent, Subgroup.mem_bot] at hu
  exact hu

theorem typeIIo_centralizes_J₂ (h : Wr p T M J₁ J₂ z₁) {c a : G} (hc : conjSub c J₁ = J₂)
    (hca : a * c = c * a) (ha : a ∈ Subgroup.centralizer (J₁ : Set G)) : a = 1 := by
  refine typeIIo_cent_eq_one h (fun g hg => (Subgroup.mem_centralizer_iff.mp ha g hg)) ?_
  intro g' hg'
  rw [← hc, mem_conjSub_iff] at hg'
  obtain ⟨g, hg, rfl⟩ : ∃ g ∈ J₁, g' = c * g * c⁻¹ := ⟨c⁻¹ * g' * c, hg', by group⟩
  have h1 : g * a = a * g := Subgroup.mem_centralizer_iff.mp ha g hg
  have hconj : c * a * c⁻¹ = a := by rw [← hca]; group
  calc c * g * c⁻¹ * a = c * g * c⁻¹ * (c * a * c⁻¹) := by rw [hconj]
    _ = c * (g * a) * c⁻¹ := by group
    _ = c * (a * g) * c⁻¹ := by rw [h1]
    _ = (c * a * c⁻¹) * (c * g * c⁻¹) := by group
    _ = a * (c * g * c⁻¹) := by rw [hconj]

theorem typeIIo_inner_in_X (h : Wr p T M J₁ J₂ z₁) {c a y y₀ : G} (hc : conjSub c J₁ = J₂)
    (hca : a * c = c * a) (hy : y ∈ J₁) (hy₀ : y₀ ∈ Subgroup.centralizer (J₁ : Set G))
    (hay : a = y * y₀) : a ∈ J₁ ⊔ J₂ := by
  obtain ⟨y', hy'def⟩ : ∃ y', y' = c * y * c⁻¹ := ⟨_, rfl⟩
  have hy'J : y' ∈ J₂ := by
    rw [hy'def, ← hc]
    exact mem_conjSub_of_mem hy
  have hconj : c * a * c⁻¹ = a := by rw [← hca]; group
  have hyy₀ : ∀ g ∈ J₁, g * y₀ = y₀ * g := fun g hg => Subgroup.mem_centralizer_iff.mp hy₀ g hg
  have hag : ∀ g ∈ J₁, a * g * a⁻¹ = y * g * y⁻¹ := by
    intro g hg
    rw [hay]
    calc y * y₀ * g * (y * y₀)⁻¹ = y * (y₀ * g * y₀⁻¹) * y⁻¹ := by group
      _ = y * g * y⁻¹ := by rw [← hyy₀ g hg]; group
  have hyJ₂ : ∀ x ∈ J₂, y * x = x * y := fun x hx => h.comm y hy x hx
  have hu : (y * y')⁻¹ * a = 1 := by
    refine typeIIo_cent_eq_one h ?_ ?_
    · intro g hg
      have hu : (y * y')⁻¹ * a = y'⁻¹ * y₀ := by rw [hay]; group
      rw [hu]
      have h1 : g * y'⁻¹ = y'⁻¹ * g := h.comm g hg y'⁻¹ (J₂.inv_mem hy'J)
      calc g * (y'⁻¹ * y₀) = (g * y'⁻¹) * y₀ := by group
        _ = y'⁻¹ * g * y₀ := by rw [h1]
        _ = y'⁻¹ * (g * y₀) := by group
        _ = y'⁻¹ * (y₀ * g) := by rw [hyy₀ g hg]
        _ = y'⁻¹ * y₀ * g := by group
    · intro g' hg'
      rw [← hc, mem_conjSub_iff] at hg'
      obtain ⟨g, hg, rfl⟩ : ∃ g ∈ J₁, g' = c * g * c⁻¹ := ⟨c⁻¹ * g' * c, hg', by group⟩
      have hg'J : c * g * c⁻¹ ∈ J₂ := by
        rw [← hc]
        exact mem_conjSub_of_mem hg
      have hL : y * y' * (c * g * c⁻¹) * (y * y')⁻¹ = y' * (c * g * c⁻¹) * y'⁻¹ := by
        have hx : y' * (c * g * c⁻¹) * y'⁻¹ ∈ J₂ :=
          J₂.mul_mem (J₂.mul_mem hy'J hg'J) (J₂.inv_mem hy'J)
        calc y * y' * (c * g * c⁻¹) * (y * y')⁻¹
            = y * (y' * (c * g * c⁻¹) * y'⁻¹) * y⁻¹ := by group
          _ = (y' * (c * g * c⁻¹) * y'⁻¹) * y * y⁻¹ := by rw [hyJ₂ _ hx]
          _ = y' * (c * g * c⁻¹) * y'⁻¹ := by group
      have hR : a * (c * g * c⁻¹) * a⁻¹ = y' * (c * g * c⁻¹) * y'⁻¹ := by
        calc a * (c * g * c⁻¹) * a⁻¹
            = (c * a * c⁻¹) * (c * g * c⁻¹) * (c * a * c⁻¹)⁻¹ := by rw [hconj]
          _ = c * (a * g * a⁻¹) * c⁻¹ := by group
          _ = c * (y * g * y⁻¹) * c⁻¹ := by rw [hag g hg]
          _ = y' * (c * g * c⁻¹) * y'⁻¹ := by rw [hy'def]; group
      have E1 : y * y' * (c * g * c⁻¹) * (y * y')⁻¹ * a = a * (c * g * c⁻¹) := by
        rw [hL, ← hR]
        group
      calc c * g * c⁻¹ * ((y * y')⁻¹ * a)
          = (y * y')⁻¹ * (y * y' * (c * g * c⁻¹) * (y * y')⁻¹ * a) := by group
        _ = (y * y')⁻¹ * (a * (c * g * c⁻¹)) := by rw [E1]
        _ = (y * y')⁻¹ * a * (c * g * c⁻¹) := by group
  have hay' : a = y * y' := by
    calc a = (y * y') * ((y * y')⁻¹ * a) := by group
      _ = y * y' := by rw [hu, mul_one]
  rw [hay']
  exact Subgroup.mul_mem_sup hy hy'J

theorem typeIIo_le_commutator {r : ℕ} (hr : Odd r) {P A : Subgroup G} (hP : IsPGroup r P) {w : G}
    (hw : w ∈ A) (hwinv : ∀ x ∈ P, w * x * w⁻¹ = x⁻¹) : P ≤ ⁅P, A⁆ := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, hj⟩ := e22ptor_exists_sq hr hk'
  have hxj : x ^ j ∈ P := P.pow_mem hx j
  have h1 : ⁅x ^ j, w⁆ = x := by
    have h2 := hwinv (x ^ j) hxj
    have h3 : ⁅x ^ j, w⁆ = x ^ j * (w * x ^ j * w⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h3, h2, inv_inv, ← sq]
    exact hj
  rw [← h1]
  exact Subgroup.commutator_mem_commutator hxj hw

variable [Finite G]

theorem typeIIo_J_ne (h : Wr p T M J₁ J₂ z₁) : J₁ ≠ J₂ := by
  intro heq
  have hbot : J₁ = ⊥ := by
    have := h.disj
    rwa [← heq, inf_idem] at this
  obtain ⟨a, b, hab⟩ := h.nonab₁
  apply hab
  have ha : a = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall J₁).mp hbot a a.2)
  have hb : b = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall J₁).mp hbot b b.2)
  rw [ha, hb]

theorem typeIIo_conj_swap (h : Wr p T M J₁ J₂ z₁) {c : G} (hcT : c ∈ T)
    (hc : conjSub c J₁ = J₂) : conjSub c J₂ = J₁ := by
  have h1 : conjSub c J₂ = conjSub (c * c) J₁ := by rw [conjSub_mul, hc]
  rcases h.perm (c * c) (T.mul_mem hcT hcT) with h2 | h2
  · rw [h1, h2]
  · exfalso
    have h3 : conjSub c J₂ = J₂ := by rw [h1, h2]
    have h4 : conjSub c J₂ = conjSub c J₁ := by rw [h3, hc]
    exact typeIIo_J_ne h ((conjSub_inj c).mp h4).symm

end Outer

theorem typeII_outer {G : Type} [Group G] [Finite G] {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ : G}
    (h : Wr p T M J₁ J₂ z₁) {A : Subgroup G} (hAT : A ≤ T) (hAab : IsElemAbelian 2 A)
    (hA4 : 4 ≤ Nat.card A)
    (hc : ¬ T ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (J₁ : Set G))
    (hAS : A ≤ Subgroup.normalizer (J₁ : Set G)) (hAX : ¬ A ≤ J₁ ⊔ J₂) :
    ∃ K : Subgroup G, E1.IsE 1 ⊤ T A K ∧ ¬ K ≤ M := by
  obtain ⟨c, hcR, hcN⟩ : ∃ c ∈ T ⊓ Subgroup.centralizer (A : Set G),
      c ∉ Subgroup.normalizer (J₁ : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hc fun c hc => hcon c hc
  have hcT : c ∈ T := hcR.1
  have hcA : ∀ a ∈ A, a * c = c * a := fun a ha => Subgroup.mem_centralizer_iff.mp hcR.2 a ha
  have hcJ : conjSub c J₁ = J₂ := by
    rcases h.perm c hcT with h1 | h1
    · exact absurd (conjSub_eq_iff_mem_normalizer.mp h1) hcN
    · exact h1
  have hcJ' : conjSub c J₂ = J₁ := typeIIo_conj_swap h hcT hcJ
  have hAC : ∀ a ∈ A, a ∈ Subgroup.centralizer (J₁ : Set G) → a = 1 := fun a ha hac =>
    typeIIo_centralizes_J₂ h hcJ (hcA a ha) hac
  obtain ⟨a₀, ha₀A, ha₀X⟩ : ∃ a ∈ A, a ∉ J₁ ⊔ J₂ := by
    by_contra hcon
    push Not at hcon
    exact hAX fun a ha => hcon a ha
  have hAD : ∃ a ∈ A, ∀ y ∈ J₁, ∀ y₀ ∈ Subgroup.centralizer (J₁ : Set G), a ≠ y * y₀ :=
    ⟨a₀, ha₀A, fun y hy y₀ hy₀ hay =>
      ha₀X (typeIIo_inner_in_X h hcJ (hcA a₀ ha₀A) hy hy₀ hay)⟩
  set S : Subgroup G := T ⊓ Subgroup.normalizer (J₁ : Set G) with hSdef
  set Q : Subgroup G := J₁ ⊔ S with hQdef
  have hJN : J₁ ≤ Subgroup.normalizer (J₁ : Set G) := Subgroup.le_normalizer
  have hSN : S ≤ Subgroup.normalizer (J₁ : Set G) := inf_le_right
  have hQN : Q ≤ Subgroup.normalizer (J₁ : Set G) := sup_le hJN hSN
  have hDQ : J₁ ≤ Q := le_sup_left
  have hSQ : S ≤ Q := le_sup_right
  have hAQ : A ≤ Q := (le_inf hAT hAS).trans hSQ
  have hDn : (J₁.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDQ).mpr hQN
  have hTQS : T ⊓ Q = S :=
    le_antisymm (le_inf inf_le_left (inf_le_right.trans hQN)) (le_inf inf_le_left hSQ)
  have hS2 : IsPGroup 2 ↥S := h.sylow.isPGroup.to_le inf_le_left
  have hsyl : IsSylowIn 2 (S ⊓ J₁) J₁ := by
    have : S ⊓ J₁ = T ⊓ J₁ :=
      le_antisymm (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (le_inf (le_inf inf_le_left (inf_le_right.trans hJN)) inf_le_right)
    rw [this]
    exact h.sylow_J₁
  have hTQ : IsSylowIn 2 (T ⊓ Q) Q := by
    rw [hTQS]
    exact E1.isSylowIn_two_of_sup_inf hSN hS2 hsyl
  have hzc : ∀ x ∈ T ⊓ Q, z₁ * x = x * z₁ := fun x hx => h.z₁_central x ⟨hx.1, hQN hx.2⟩
  obtain ⟨r, P₀, b, w, hr, hr2, hP₀J, hP₀ne, hP₀g, hAcard, hbA, hb1, hwA, hwz, hAn, hbc, hzinv,
      htn⟩ := typeIIo_local h.p_prime h.p_mod h.p_ge hAT hAQ hAab hA4 hDQ hDn h.psl₁ h.simple₁
    h.nonab₁ hTQ hAD hAC h.z₁_mem h.z₁_ord hzc
  have hr' : Odd r := hr.odd_of_ne_two hr2
  set P₁ : Subgroup G := conjSub c P₀ with hP₁def
  have hP₁J : P₁ ≤ J₂ := hcJ ▸ conjSub_mono c hP₀J
  have hP₁g : IsPGroup r P₁ := hP₀g.map (MulAut.conj c).toMonoidHom
  have hyx : ∀ y ∈ P₁, ∀ x ∈ P₀, y * x * y⁻¹ = x := by
    intro y hy x hx
    rw [← h.comm x (hP₀J hx) y (hP₁J hy)]
    group
  have hP₁N : P₁ ≤ Subgroup.normalizer (P₀ : Set G) := by
    intro y hy
    apply mem_normalizer_of_conj_mem
    intro x hx
    rw [hyx y hy x hx]
    exact hx
  set P : Subgroup G := P₀ ⊔ P₁ with hPdef
  have hPg : IsPGroup r P := hP₀g.to_sup_of_normal_left' hP₁g hP₁N
  have hPne : P ≠ ⊥ := fun hbot => hP₀ne (le_bot_iff.mp (le_sup_left.trans hbot.le))
  have hconjN : ∀ s ∈ T ⊓ Subgroup.centralizer (A : Set G), s ∈ Subgroup.normalizer (J₁ : Set G) →
      conjSub s P = P := by
    intro s hs hsN
    have hsS : s ∈ T ⊓ Q := ⟨hs.1, hSQ ⟨hs.1, hsN⟩⟩
    have hsA : ∀ a ∈ A, s * a = a * s := fun a ha =>
      (Subgroup.mem_centralizer_iff.mp hs.2 a ha).symm
    have h1 : conjSub s P₀ = P₀ := conjSub_eq_iff_mem_normalizer.mpr (htn s hsS hsA)
    have hsJ₂ : conjSub s J₂ = J₂ := by
      have h2 : s ∈ T ⊓ Subgroup.normalizer (J₂ : Set G) := h.normalizer_eq ▸ (⟨hs.1, hsN⟩ :
        s ∈ T ⊓ Subgroup.normalizer (J₁ : Set G))
      exact conjSub_eq_iff_mem_normalizer.mpr h2.2
    have hc'J₂ : conjSub c⁻¹ J₂ = J₁ := by
      rw [← hcJ, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have hcsN : c⁻¹ * s * c ∈ Subgroup.normalizer (J₁ : Set G) := by
      apply conjSub_eq_iff_mem_normalizer.mp
      calc conjSub (c⁻¹ * s * c) J₁ = conjSub (c⁻¹ * s) (conjSub c J₁) := conjSub_mul _ _ _
        _ = conjSub c⁻¹ (conjSub s J₂) := by rw [hcJ, conjSub_mul]
        _ = J₁ := by rw [hsJ₂, hc'J₂]
    have hcsT : c⁻¹ * s * c ∈ T := T.mul_mem (T.mul_mem (T.inv_mem hcT) hs.1) hcT
    have hcsA : ∀ a ∈ A, (c⁻¹ * s * c) * a = a * (c⁻¹ * s * c) := by
      intro a ha
      have e1 : c * a = a * c := (hcA a ha).symm
      have e2 : s * a = a * s := hsA a ha
      have e3 : c⁻¹ * a = a * c⁻¹ := by
        calc c⁻¹ * a = c⁻¹ * (a * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * a) * c⁻¹ := by rw [← hcA a ha]
          _ = a * c⁻¹ := by group
      calc c⁻¹ * s * c * a = c⁻¹ * s * (c * a) := by group
        _ = c⁻¹ * s * (a * c) := by rw [e1]
        _ = c⁻¹ * (s * a) * c := by group
        _ = c⁻¹ * (a * s) * c := by rw [e2]
        _ = (c⁻¹ * a) * s * c := by group
        _ = (a * c⁻¹) * s * c := by rw [e3]
        _ = a * (c⁻¹ * s * c) := by group
    have h2 : conjSub (c⁻¹ * s * c) P₀ = P₀ :=
      conjSub_eq_iff_mem_normalizer.mpr (htn _ ⟨hcsT, hSQ ⟨hcsT, hcsN⟩⟩ hcsA)
    have h3 : conjSub s P₁ = P₁ := by
      calc conjSub s P₁ = conjSub s (conjSub c P₀) := rfl
        _ = conjSub (s * c) P₀ := (conjSub_mul s c P₀).symm
        _ = conjSub (c * (c⁻¹ * s * c)) P₀ := by congr 1; group
        _ = conjSub c (conjSub (c⁻¹ * s * c) P₀) := conjSub_mul _ _ _
        _ = P₁ := by rw [h2]
    calc conjSub s P = conjSub s P₀ ⊔ conjSub s P₁ := Subgroup.map_sup _ _ _
      _ = P := by rw [h1, h3]
  have hconjc : conjSub c P = P := by
    have hccJ : conjSub (c * c) J₁ = J₁ := by rw [conjSub_mul, hcJ, hcJ']
    have hccN : c * c ∈ Subgroup.normalizer (J₁ : Set G) := conjSub_eq_iff_mem_normalizer.mp hccJ
    have hccT : c * c ∈ T := T.mul_mem hcT hcT
    have hccA : ∀ a ∈ A, (c * c) * a = a * (c * c) := by
      intro a ha
      calc c * c * a = c * (c * a) := by group
        _ = c * (a * c) := by rw [← hcA a ha]
        _ = c * a * c := by group
        _ = a * c * c := by rw [hcA a ha]
        _ = a * (c * c) := by group
    have h2 : conjSub (c * c) P₀ = P₀ :=
      conjSub_eq_iff_mem_normalizer.mpr (htn _ ⟨hccT, hSQ ⟨hccT, hccN⟩⟩ hccA)
    calc conjSub c P = conjSub c P₀ ⊔ conjSub c P₁ := Subgroup.map_sup _ _ _
      _ = P₁ ⊔ conjSub (c * c) P₀ := by rw [conjSub_mul]
      _ = P₁ ⊔ P₀ := by rw [h2]
      _ = P := sup_comm _ _
  have hτP : E1.tauOf ⊤ T A ≤ Subgroup.normalizer (P : Set G) := by
    rw [h.tau_eq A]
    intro t ht
    by_cases htN : t ∈ Subgroup.normalizer (J₁ : Set G)
    · exact conjSub_eq_iff_mem_normalizer.mp (hconjN t ht htN)
    · have htJ : conjSub t J₁ = J₂ := (h.perm t ht.1).resolve_left fun h1 =>
        htN (conjSub_eq_iff_mem_normalizer.mp h1)
      have htJ' : conjSub t J₂ = J₁ := typeIIo_conj_swap h ht.1 htJ
      have hc'J : conjSub c⁻¹ J₁ = J₂ := by
        rw [← hcJ', ← conjSub_mul, inv_mul_cancel, conjSub_one]
      have hs : t * c⁻¹ ∈ Subgroup.normalizer (J₁ : Set G) := by
        apply conjSub_eq_iff_mem_normalizer.mp
        rw [conjSub_mul, hc'J, htJ']
      have hsR : t * c⁻¹ ∈ T ⊓ Subgroup.centralizer (A : Set G) :=
        (T ⊓ Subgroup.centralizer (A : Set G)).mul_mem ht
          ((T ⊓ Subgroup.centralizer (A : Set G)).inv_mem hcR)
      have h1 := conjSub_eq_iff_mem_normalizer.mp (hconjN _ hsR hs)
      have h2 := conjSub_eq_iff_mem_normalizer.mp hconjc
      have : t = (t * c⁻¹) * c := by group
      rw [this]
      exact Subgroup.mul_mem _ h1 h2
  have hAnP : A ≤ Subgroup.normalizer (P : Set G) := by
    intro a ha
    apply conjSub_eq_iff_mem_normalizer.mp
    have h1 : conjSub a P₀ = P₀ := conjSub_eq_iff_mem_normalizer.mpr (hAn a ha)
    have h3 : conjSub a P₁ = P₁ := by
      calc conjSub a P₁ = conjSub a (conjSub c P₀) := rfl
        _ = conjSub (a * c) P₀ := (conjSub_mul a c P₀).symm
        _ = conjSub (c * a) P₀ := by rw [hcA a ha]
        _ = conjSub c (conjSub a P₀) := conjSub_mul _ _ _
        _ = P₁ := by rw [h1]
    calc conjSub a P = conjSub a P₀ ⊔ conjSub a P₁ := Subgroup.map_sup _ _ _
      _ = P := by rw [h1, h3]
  have hw₀ : ∀ x ∈ P₀, w * x * w⁻¹ = x⁻¹ := fun x hx => by
    rw [hwz x (hP₀J hx)]
    exact hzinv x hx
  have hw₁ : ∀ y ∈ P₁, w * y * w⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ : ∃ x ∈ P₀, y = c * x * c⁻¹ :=
      ⟨c⁻¹ * y * c, mem_conjSub_iff.mp hy, by group⟩
    have hwc : w * c = c * w := hcA w hwA
    have hconj : c⁻¹ * w * c = w := by
      calc c⁻¹ * w * c = c⁻¹ * (w * c) := by group
        _ = c⁻¹ * (c * w) := by rw [hwc]
        _ = w := by group
    calc w * (c * x * c⁻¹) * w⁻¹ = c * ((c⁻¹ * w * c) * x * (c⁻¹ * w * c)⁻¹) * c⁻¹ := by group
      _ = c * (w * x * w⁻¹) * c⁻¹ := by rw [hconj]
      _ = c * x⁻¹ * c⁻¹ := by rw [hw₀ x hx]
      _ = (c * x * c⁻¹)⁻¹ := by group
  have hcomm : ⁅P, A⁆ = P := by
    refine le_antisymm (E1.commutator_le_of_le_normalizer hAnP) (sup_le ?_ ?_)
    · exact (typeIIo_le_commutator hr' hP₀g hwA hw₀).trans
        (Subgroup.commutator_mono le_sup_left le_rfl)
    · exact (typeIIo_le_commutator hr' hP₁g hwA hw₁).trans
        (Subgroup.commutator_mono le_sup_right le_rfl)
  have hb2 : orderOf b = 2 := by
    have : b ^ 2 = 1 := hAab.2 b hbA
    exact orderOf_eq_prime this hb1
  have hbP : ∀ x ∈ P, x * b = b * x := by
    have hle : P ≤ Subgroup.centralizer ({b} : Set G) := by
      refine sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hbc x hx).symm) ?_
      intro y hy
      obtain ⟨x, hx, rfl⟩ : ∃ x ∈ P₀, y = c * x * c⁻¹ :=
      ⟨c⁻¹ * y * c, mem_conjSub_iff.mp hy, by group⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hbc' : b * c = c * b := hcA b hbA
      have hconj' : c * b * c⁻¹ = b := by rw [← hbc']; group
      calc c * x * c⁻¹ * b = (c * x * c⁻¹) * (c * b * c⁻¹) := by rw [hconj']
        _ = c * (x * b) * c⁻¹ := by group
        _ = c * (b * x) * c⁻¹ := by rw [hbc x hx]
        _ = (c * b * c⁻¹) * (c * x * c⁻¹) := by group
        _ = b * (c * x * c⁻¹) := by rw [hconj']
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hBA : Subgroup.zpowers b ≤ A := Subgroup.zpowers_le.mpr hbA
  have hBc : Subgroup.zpowers b ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr hbP)
  have hBidx : (Subgroup.zpowers b).relIndex A ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.zpowers b) (K := A)
    rw [inf_eq_left.mpr hBA, Nat.card_zpowers, hb2, hAcard] at h1
    omega
  have hE := (E1.isE_one_sup hr hr2 h.sylow hAT hAab hPg hPne hτP hcomm hBA hBc hBidx).1
  refine ⟨P ⊔ E1.tauOf ⊤ T A, hE, fun hKM => ?_⟩
  have hP₀M : P₀ ≤ M := le_sup_left.trans (le_sup_left.trans hKM)
  apply hP₀ne
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  have hxMJ : x ∈ M ⊓ J₁ := ⟨hP₀M hx, hP₀J hx⟩
  rw [h.M_J₁] at hxMJ
  have hxz : x * z₁ = z₁ * x := Subgroup.mem_centralizer_singleton_iff.mp hxMJ.1
  have hxinv : x = x⁻¹ := by
    calc x = z₁ * x * z₁⁻¹ := by rw [← hxz]; group
      _ = x⁻¹ := hzinv x hx
  have hsq : x ^ 2 = 1 := by
    rw [sq]
    calc x * x = x * x⁻¹ := by rw [← hxinv]
      _ = 1 := mul_inv_cancel x
  obtain ⟨k, hk⟩ := hP₀g ⟨x, hx⟩
  have hk' : x ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, hj⟩ := e22ptor_exists_sq hr' hk'
  rw [← hj, ← pow_mul, mul_comm, pow_mul, hsq, one_pow]

end CFSG.Quasithin.E2.E22N
