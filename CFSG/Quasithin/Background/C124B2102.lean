module

public import CFSG.Quasithin.Background.C124FStar
public import CFSG.Quasithin.Background.C124Offender
public import CFSG.Quasithin.Background.B2FactorizationSolvable
public import CFSG.Quasithin.Background.InternalSecISec
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

section Basic

theorem pCoreOf_le_centralizer {X V : Subgroup G} (hred : IsTwoReducedIn X V) :
    pCoreOf 2 X ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hred.2.2.2 _ (pCoreOf_le 2 X) (le_normalizer_pCoreOf 2 X) fun d hd => ?_
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 X) ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have h1 : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [h1]
  exact Subgroup.one_mem _

omit [Finite G] in
theorem le_pCoreOf_of_reduced {X V : Subgroup G} (hred : IsTwoReducedIn X V) :
    V ≤ pCoreOf 2 X :=
  le_pCoreOf_of_le_normalizer 2 hred.1 hred.2.1 (B2F.isPGroup_of_isElemAbelian hred.2.2.1)

omit [Finite G] in
theorem conj_mem_centralizer_of_le {X V : Subgroup G} (hXN : X ≤ Subgroup.normalizer (V : Set G))
    {x c : G} (hx : x ∈ X) (hc : c ∈ Subgroup.centralizer (V : Set G)) :
    x * c * x⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
  (Subgroup.mem_normalizer_iff.1 (B2F.normalizer_le_normalizer_centralizer V (hXN hx)) c).1 hc

omit [Finite G] in
theorem exists_pow_mem_of_prod {X L T : Subgroup G} (hLX : L ≤ X)
    (hn : X ≤ Subgroup.normalizer (L : Set G)) (hTX : T ≤ X) (hT : IsPGroup 2 T) {x : G}
    (hx : x ∈ X) (hprod : ∃ l ∈ L, ∃ t ∈ T, x = l * t) : ∃ k : ℕ, x ^ 2 ^ k ∈ L := by
  have hnorm : (L.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 hn
  obtain ⟨l, hl, t, ht, rfl⟩ := hprod
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htX : t ∈ X := hTX ht
  refine ⟨k, ?_⟩
  have hmk : (QuotientGroup.mk ⟨l * t, hx⟩ : ↥X ⧸ L.subgroupOf X) =
      QuotientGroup.mk ⟨t, htX⟩ := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (l * t)⁻¹ * t ∈ L
    have e : (l * t)⁻¹ * t = t⁻¹ * l⁻¹ * t⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (hn (X.inv_mem htX)) l⁻¹).1 (L.inv_mem hl)
  have hone : (QuotientGroup.mk ⟨l * t, hx⟩ : ↥X ⧸ L.subgroupOf X) ^ (2 ^ k) = 1 := by
    rw [hmk, ← QuotientGroup.mk_pow]
    have : (⟨t, htX⟩ : ↥X) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this]; rfl
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hone
  exact Subgroup.mem_subgroupOf.1 hone

end Basic

section Centralizer

open scoped commutatorElement

omit [Finite G] in
theorem pCoreOf_eq_map_pCore (X : Subgroup G) :
    pCoreOf 2 X = (CFSG.pCore 2 ↥X).map X.subtype := CFSG.openPCoreOf_eq_map_pCore 2 X

theorem commutator_centralizer_le_pCoreOf {X V L : Subgroup G} (hred : IsTwoReducedIn X V)
    (hLX : L ≤ X) (hn : X ≤ Subgroup.normalizer (L : Set G)) (hVL : ⁅V, L⁆ ≠ ⊥)
    (hLq : CFSG.Open.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∨
      Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) :
    ∀ d ∈ X ⊓ Subgroup.centralizer (V : Set G), ∀ l ∈ L,
      d * l * d⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  intro d hd l hl
  have hdX : d ∈ X := hd.1
  have hdC : d ∈ Subgroup.centralizer (V : Set G) := hd.2
  have hdL : d ∈ Subgroup.normalizer (L : Set G) := hn hdX
  set K : Subgroup G := L ⊓ Subgroup.centralizer (V : Set G) with hK
  have hcK : ∀ y ∈ L, d * y * d⁻¹ * y⁻¹ ∈ K := by
    intro y hy
    have h1 : d * y * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hdL y).1 hy
    refine ⟨L.mul_mem h1 (L.inv_mem hy), ?_⟩
    have h2 : y * d⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
      conj_mem_centralizer_of_le hred.2.1 (hLX hy) (Subgroup.inv_mem _ hdC)
    have e : d * y * d⁻¹ * y⁻¹ = d * (y * d⁻¹ * y⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hdC h2
  have hNX : pCoreOf 2 L ≤ pCoreOf 2 X := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLX)
      (hn.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)
  have hNK : pCoreOf 2 L ≤ K := le_inf (pCoreOf_le 2 L) (hNX.trans (pCoreOf_le_centralizer hred))
  have hKnorm : (K.subgroupOf L).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 hx.1) (L.inv_mem g.2), ?_⟩
    have := conj_mem_centralizer_of_le hred.2.1 (hLX g.2) hx.2
    simpa using this
  set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hker : π.ker = CFSG.pCore 2 ↥L := QuotientGroup.ker_mk' _
  have hNsub : CFSG.pCore 2 ↥L ≤ K.subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    apply hNK
    rw [pCoreOf_eq_map_pCore]
    exact ⟨x, hx, rfl⟩
  set A : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := (K.subgroupOf L).map π with hA
  have hAnormal : A.Normal := Subgroup.Normal.map hKnorm π (QuotientGroup.mk'_surjective _)
  have hAne : A ≠ ⊤ := by
    intro htop
    apply hVL
    have hLK : L ≤ K := by
      intro y hy
      have : π ⟨y, hy⟩ ∈ A := by rw [htop]; trivial
      obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.1 this
      have h2 : k⁻¹ * ⟨y, hy⟩ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hkπ, inv_mul_cancel]
      rw [hker] at h2
      have h3 : k⁻¹ * ⟨y, hy⟩ ∈ K.subgroupOf L := hNsub h2
      have h5 : ⟨y, hy⟩ ∈ K.subgroupOf L := by
        have := Subgroup.mul_mem _ hk h3
        simpa using this
      exact h5
    have hLC : L ≤ Subgroup.centralizer (V : Set G) := fun y hy => (hLK hy).2
    rw [← Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hLC
  let ψ : ↥L ≃* ↥L := L.normalizerMonoidHom ⟨d, hdL⟩
  have hψ_coe : ∀ y : ↥L, ((ψ y : ↥L) : G) = d * y * d⁻¹ := fun y =>
    L.normalizerMonoidHom_apply_apply_coe ⟨d, hdL⟩ y
  have hψK : ∀ y : ↥L, ψ y * y⁻¹ ∈ K.subgroupOf L := by
    intro y
    rw [Subgroup.mem_subgroupOf]
    have := hcK y y.2
    simpa [hψ_coe y, mul_assoc] using this
  have hAψ : ∀ y : ↥L, π (ψ y * y⁻¹) ∈ A := fun y => ⟨_, hψK y, rfl⟩
  suffices hmain : ∀ y : ↥L, ψ y * y⁻¹ ∈ CFSG.pCore 2 ↥L by
    have h1 := hmain ⟨l, hl⟩
    rw [pCoreOf_eq_map_pCore]
    refine ⟨_, h1, ?_⟩
    simp [hψ_coe, mul_assoc]
  rcases hLq with hq | h3
  ·
    have hAc : A ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      have := hAnormal
      exact CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hq A hAne
    have hψc : CFSG.pCore 2 ↥L ≤ (CFSG.pCore 2 ↥L).comap ψ.toMonoidHom :=
      Subgroup.characteristic_iff_le_comap.1 inferInstance ψ
    let ψ' : (↥L ⧸ CFSG.pCore 2 ↥L) →* (↥L ⧸ CFSG.pCore 2 ↥L) :=
      QuotientGroup.map _ _ ψ.toMonoidHom hψc
    have hψ'π : ∀ y : ↥L, ψ' (QuotientGroup.mk y) * (QuotientGroup.mk y)⁻¹ = π (ψ y * y⁻¹) := by
      intro y
      simp [ψ', π]
    have key : ∀ p, ψ' p * p⁻¹ ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      intro p
      induction p using QuotientGroup.induction_on with
      | H y =>
        rw [hψ'π]
        exact hAc (hAψ y)
    have hid := eq_of_central_ratio hq.1 ψ' key
    intro y
    have h1 : π (ψ y * y⁻¹) = 1 := by
      rw [← hψ'π, hid (QuotientGroup.mk y), mul_inv_cancel]
    rw [← hker]
    exact h1
  · have : Fact (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)).Prime := ⟨by rw [h3]; exact Nat.prime_three⟩
    have hA0 : A = ⊥ := (A.eq_bot_or_eq_top_of_prime_card).resolve_right hAne
    intro y
    have h1 : π (ψ y * y⁻¹) ∈ A := hAψ y
    rw [hA0, Subgroup.mem_bot] at h1
    rw [← hker]
    exact h1

end Centralizer

section Sylow

omit [Finite G] in
theorem conj_mem_sup {S₁ S₂ : Subgroup G} {g : G} (h1 : ∀ x ∈ S₁, g * x * g⁻¹ ∈ S₁ ⊔ S₂)
    (h2 : ∀ x ∈ S₂, g * x * g⁻¹ ∈ S₁ ⊔ S₂) : ∀ x ∈ S₁ ⊔ S₂, g * x * g⁻¹ ∈ S₁ ⊔ S₂ := by
  intro x hx
  have : (S₁ ⊔ S₂ : Subgroup G) ≤ (S₁ ⊔ S₂).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun y hy => h1 y hy) (fun y hy => h2 y hy)
  exact this hx

omit [Finite G] in
theorem mem_normalizer_of_conj {S : Subgroup G} {g : G} (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S)
    (h' : ∀ x ∈ S, g⁻¹ * x * g ∈ S) : g ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  have := h' _ hy
  simpa [mul_assoc] using this

theorem inf_centralizer_eq_pCoreOf {X V L T : Subgroup G} (hred : IsTwoReducedIn X V)
    (hT : IsSylowTwoOf T X) (hLX : L ≤ X) (hn : X ≤ Subgroup.normalizer (L : Set G))
    (hLT : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hVL : ⁅V, L⁆ ≠ ⊥)
    (hLq : CFSG.Open.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∨
      Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) :
    T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 X with hQ
  set D := T ⊓ Subgroup.centralizer (V : Set G) with hD
  have hQT : Q ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hQC : Q ≤ Subgroup.centralizer (V : Set G) := pCoreOf_le_centralizer hred
  have hQn : ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := fun x hx q hq =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 X hx) q).1 hq
  apply le_antisymm _ (le_inf hQT hQC)
  set S := D ⊔ Q with hS
  have hST : S ≤ T := sup_le inf_le_left hQT
  have hSX : S ≤ X := hST.trans hT.1
  have hS2 : IsPGroup 2 S := hT.2.1.to_le hST
  have hTgen : ∀ g ∈ T, ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
    intro g hg
    refine conj_mem_sup (fun x hx => ?_) (fun x hx => ?_)
    · refine Subgroup.mem_sup_left ⟨T.mul_mem (T.mul_mem hg hx.1) (T.inv_mem hg), ?_⟩
      exact conj_mem_centralizer_of_le hred.2.1 (hT.1 hg) hx.2
    · exact Subgroup.mem_sup_right (hQn g (hT.1 hg) x hx)
  have hLgen : ∀ g ∈ L, ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
    intro g hg
    refine conj_mem_sup (fun x hx => ?_) (fun x hx => ?_)
    · have hxX : x ∈ X ⊓ Subgroup.centralizer (V : Set G) := ⟨hT.1 hx.1, hx.2⟩
      have hc := commutator_centralizer_le_pCoreOf hred hLX hn hVL hLq x hxX g hg
      have hcQ : x * g * x⁻¹ * g⁻¹ ∈ Q := by
        have : pCoreOf 2 L ≤ Q :=
          le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLX)
            (hn.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)
        exact this hc
      have e : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
      have hq : g * x * g⁻¹ * x⁻¹ ∈ Q := by
        have h1 : (x * g * x⁻¹ * g⁻¹)⁻¹ = g * x * g⁻¹ * x⁻¹ := by group
        rw [← h1]
        exact Q.inv_mem hcQ
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hq) (Subgroup.mem_sup_left hx)
    · exact Subgroup.mem_sup_right (hQn g (hLX hg) x hx)
  have hXn : X ≤ Subgroup.normalizer (S : Set G) := by
    intro x hx
    obtain ⟨l, hl, t, ht, rfl⟩ := hLT x hx
    have hl' : l ∈ Subgroup.normalizer (S : Set G) :=
      mem_normalizer_of_conj (hLgen l hl) (by simpa using hLgen l⁻¹ (L.inv_mem hl))
    have ht' : t ∈ Subgroup.normalizer (S : Set G) :=
      mem_normalizer_of_conj (hTgen t ht) (by simpa using hTgen t⁻¹ (T.inv_mem ht))
    exact Subgroup.mul_mem _ hl' ht'
  have hSQ : S ≤ Q := le_pCoreOf_of_le_normalizer 2 hSX hXn hS2
  exact le_sup_left.trans hSQ

end Sylow

section Image

variable {X V L T : Subgroup G} (hV : IsElemAbelian 2 V)

omit [Finite G] in
theorem autI_conj_mem (hn : X ≤ Subgroup.normalizer (L : Set G)) :
    ∀ y ∈ autI hV X, ∀ l ∈ autI hV L, y * l * y⁻¹ ∈ autI hV L := by
  intro y hy l hl
  obtain ⟨x, hx, rfl⟩ := (mem_autI hV).1 hy
  obtain ⟨l₀, hl₀, rfl⟩ := (mem_autI hV).1 hl
  refine (mem_autI hV).2 ⟨x * l₀ * x⁻¹, ?_, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hn hx) l₀).1 hl₀
  · simp [map_mul, map_inv]

omit [Finite G] in
theorem autI_exists_pow_mem (hLX : L ≤ X) (hn : X ≤ Subgroup.normalizer (L : Set G))
    (hTX : T ≤ X) (hT2 : IsPGroup 2 T) (hLT : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) :
    ∀ y ∈ autI hV X, ∃ k : ℕ, y ^ 2 ^ k ∈ autI hV L := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_autI hV).1 hy
  obtain ⟨k, hk⟩ := exists_pow_mem_of_prod hLX hn hTX hT2 hx (hLT _ hx)
  refine ⟨k, (mem_autI hV).2 ⟨x ^ 2 ^ k, ?_, ?_⟩⟩
  · simpa using hk
  · simp [map_pow]

theorem pCoreOf_autI_eq_bot (hred : IsTwoReducedIn X V) : pCoreOf 2 (autI hV X) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine B2F.eq_bot_of_normal_isPGroup hV hred (pCoreOf_le 2 _) ?_ ?_
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).mpr
      (le_normalizer_pCoreOf 2 _)
  · exact pCoreOf_isPGroup 2 _

theorem pCoreOf_autI_L_eq_bot (hred : IsTwoReducedIn X V) (hLX : L ≤ X)
    (hn : X ≤ Subgroup.normalizer (L : Set G)) : pCoreOf 2 (autI hV L) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLY : autI hV L ≤ autI hV X := autI_mono hV hLX
  have hYn : autI hV X ≤ Subgroup.normalizer (autI hV L : Set (MulAut (IntMod V hV))) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro l
    refine ⟨fun hl => autI_conj_mem hV hn y hy l hl, fun hl => ?_⟩
    have := autI_conj_mem hV hn y⁻¹ ((autI hV X).inv_mem hy) _ hl
    simpa [mul_assoc] using this
  refine B2F.eq_bot_of_normal_isPGroup hV hred ((pCoreOf_le 2 _).trans hLY) ?_
    (pCoreOf_isPGroup 2 _)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer ((pCoreOf_le 2 _).trans hLY)]
  exact hYn.trans (normalizer_le_normalizer_pCoreOf 2 _) |> fun h => by
    intro y hy
    exact h hy

theorem autI_L_cases (hred : IsTwoReducedIn X V) (hLX : L ≤ X)
    (hn : X ≤ Subgroup.normalizer (L : Set G)) (hVL : ⁅V, L⁆ ≠ ⊥)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∨ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) :
    CFSG.IsQuasisimple ↥(autI hV L) ∨ Nat.card ↥(autI hV L) = 3 := by
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hLX.trans hred.2.1
  have hO2 : pCoreOf 2 (autOn L V) = ⊥ := pCoreOf_autI_L_eq_bot hV hred hLX hn
  have hnt : ¬ L ≤ Subgroup.centralizer (V : Set G) := fun h => hVL (by
    rw [← Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h)
  rcases hLq with hq | h3
  · exact Or.inl (InternalSec.isQuasisimple_autOn hLN hq hO2 hnt)
  · right
    have hle := InternalSec.pCore_le_ker_autOnHom hLN hO2
    set ρ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(autOn L V) :=
      QuotientGroup.lift _ (InternalSec.autOnHom hLN) hle with hρ
    have hρs : Function.Surjective ρ := by
      intro y
      obtain ⟨l, rfl⟩ := InternalSec.autOnHom_surjective hLN y
      exact ⟨QuotientGroup.mk l, rfl⟩
    have hdvd : Nat.card ↥(autOn L V) ∣ 3 := by
      rw [← h3]
      exact Subgroup.card_dvd_of_surjective hρs
    have hne : Nat.card ↥(autOn L V) ≠ 1 := by
      intro h1
      apply InternalSec.ker_autOnHom_ne_top hLN hnt
      rw [eq_top_iff]
      intro l _
      have hsub : Subsingleton ↥(autOn L V) := (Nat.card_eq_one_iff_unique.1 h1).1
      rw [MonoidHom.mem_ker]
      exact Subsingleton.elim _ _
    exact ((Nat.dvd_prime Nat.prime_three).1 hdvd).resolve_left hne

theorem genFitting_autI_eq (hred : IsTwoReducedIn X V) (hT : IsSylowTwoOf T X) (hLX : L ≤ X)
    (hn : X ≤ Subgroup.normalizer (L : Set G)) (hLT : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t)
    (hVL : ⁅V, L⁆ ≠ ⊥)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∨ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) :
    quasithinGenFitting (autI hV X) = autI hV L := by
  refine quasithinGenFitting_eq_of_two_group_quot (autI_mono hV hLX) (autI_conj_mem hV hn) ?_
    (autI_exists_pow_mem hV hLX hn hT.1 hT.2.1 hLT) (pCoreOf_autI_eq_bot hV hred)
  rcases autI_L_cases hV hred hLX hn hVL hLq with hq | h3
  · exact Or.inl (B1Red.isQuasisimple_to_open hq)
  · right
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (IsPGroup.of_card (p := 3) (n := 1) (by rw [h3]; simp)).isNilpotent

end Image

section Dichotomy

open scoped commutatorElement

variable {X V L T R : Subgroup G} (hV : IsElemAbelian 2 V)

theorem genFitting_ffJP_eq (hred : IsTwoReducedIn X V) (hT : IsSylowTwoOf T X)
    (hQR : pCoreOf 2 X ≤ R) (hRT : R ≤ T) (hJ : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G))
    (hLX : L ≤ X) (hn : X ≤ Subgroup.normalizer (L : Set G))
    (hLT : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hVL : ⁅V, L⁆ ≠ ⊥)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∨ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) :
    quasithinGenFitting (ffJP (offenderImagesConjIn hV X R) (autI hV X)) = autI hV L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVR : V ≤ R := (le_pCoreOf_of_reduced hred).trans hQR
  have hRX : R ≤ X := hRT.trans hT.1
  obtain ⟨hstab, -⟩ := B2_10_1_stable_in hV hred.2.1 hRX hVR hJ
  set Y := autI hV X with hY
  set Lb := autI hV L with hLb
  set P := offenderImagesConjIn hV X R with hP
  set N := ffJP P Y with hN
  have hFY : quasithinGenFitting Y = Lb :=
    genFitting_autI_eq hV hred hT hLX hn hLT hVL hLq
  have hLY : Lb ≤ Y := autI_mono hV hLX
  have hNY : N ≤ Y := iSup_le fun A => iSup_le fun _ => iSup_le fun hAY => hAY
  have hNconj : ∀ y ∈ Y, ∀ x ∈ N, y * x * y⁻¹ ∈ N := by
    intro y hy
    have : N ≤ N.comap (MulAut.conj y).toMonoidHom := by
      refine iSup_le fun A => iSup_le fun hA => iSup_le fun hAY => ?_
      intro a ha
      have hA' : A.map (MulAut.conj y).toMonoidHom ∈ P := hstab.2.2.1 A hA y hy
      have hA'Y : A.map (MulAut.conj y).toMonoidHom ≤ Y := by
        rintro _ ⟨a', ha', rfl⟩
        exact Y.mul_mem (Y.mul_mem hy (hAY ha')) (Y.inv_mem hy)
      have hle : A.map (MulAut.conj y).toMonoidHom ≤ N :=
        le_iSup₂_of_le (A.map (MulAut.conj y).toMonoidHom) hA' (le_iSup_of_le hA'Y le_rfl)
      exact hle ⟨a, ha, rfl⟩
    exact fun x hx => this hx
  have hYnN : Y ≤ Subgroup.normalizer (N : Set (MulAut (IntMod V hV))) := fun y hy =>
    mem_normalizer_of_conj (hNconj y hy) (by simpa using hNconj y⁻¹ (Y.inv_mem hy))
  have hNne : N ≠ ⊥ := by
    obtain ⟨B, hB⟩ := hstab.1
    have hoff := hstab.2.1 B hB
    intro hbot
    apply hoff.2.1
    have hle : B ≤ N := le_iSup₂_of_le B hB (le_iSup_of_le hoff.1 le_rfl)
    rw [eq_bot_iff, ← hbot]
    exact hle
  have hO2N : pCoreOf 2 N = ⊥ := by
    have h1 : pCoreOf 2 N ≤ pCoreOf 2 Y :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 N).trans hNY)
        (hYnN.trans (normalizer_le_normalizer_pCoreOf 2 N)) (pCoreOf_isPGroup 2 N)
    rw [pCoreOf_autI_eq_bot hV hred] at h1
    exact le_bot_iff.1 h1
  have hNL : ∀ n ∈ N, ∀ l ∈ Lb, n * l * n⁻¹ ∈ Lb := fun n hn' l hl =>
    autI_conj_mem hV hn n (hNY hn') l hl
  have hLN : ∀ l ∈ Lb, ∀ n ∈ N, l * n * l⁻¹ ∈ N := fun l hl n hn' =>
    hNconj l (hLY hl) n hn'
  have hLbN : Lb ≤ N := by
    by_contra hne
    have hcomm : ∀ n ∈ N, ∀ l ∈ Lb, n * l = l * n := by
      rcases autI_L_cases hV hred hLX hn hVL hLq with hq | h3
      · exact B1Red.commute_of_normal_not_le (B1Red.isQuasisimple_to_open hq) hNL hLN hne
      · have : Fact (Nat.card ↥Lb).Prime := ⟨by rw [h3]; exact Nat.prime_three⟩
        rcases ((N ⊓ Lb).subgroupOf Lb).eq_bot_or_eq_top_of_prime_card with h0 | htop
        · intro n hn' l hl
          have h1 : ⁅n, l⁆ ∈ N ⊓ Lb :=
            B1Red.commutator_le_inf_of_normalizes hNL hLN
              (Subgroup.commutator_mem_commutator hn' hl)
          have h2 : (⟨⁅n, l⁆, h1.2⟩ : ↥Lb) ∈ (N ⊓ Lb).subgroupOf Lb := h1
          rw [h0, Subgroup.mem_bot] at h2
          exact commutatorElement_eq_one_iff_mul_comm.1 (congrArg Subtype.val h2)
        · exfalso
          apply hne
          intro l hl
          have : (⟨l, hl⟩ : ↥Lb) ∈ (N ⊓ Lb).subgroupOf Lb := by rw [htop]; trivial
          exact (Subgroup.mem_subgroupOf.1 this).1
    have hNLb : N ≤ Lb := by
      intro n hn'
      have hc : n ∈ Subgroup.centralizer (Lb : Set (MulAut (IntMod V hV))) :=
        Subgroup.mem_centralizer_iff.2 fun l hl => (hcomm n hn' l hl).symm
      have hmem : n ∈ Y ⊓ Subgroup.centralizer ((quasithinGenFitting Y : Subgroup _) :
          Set (MulAut (IntMod V hV))) := by
        rw [hFY]
        exact ⟨hNY hn', hc⟩
      rw [← hFY]
      exact centralizer_quasithinGenFitting_le Y hmem
    set S : Set (MulAut (IntMod V hV)) := {a | ∃ A ∈ P, A ≤ Y ∧ a ∈ A} with hS
    have hSN : ∀ a ∈ S, a ∈ N := by
      rintro a ⟨A, hA, hAY, ha⟩
      have hle : A ≤ N := le_iSup₂_of_le A hA (le_iSup_of_le hAY le_rfl)
      exact hle ha
    have hNS : N = Subgroup.closure S := by
      apply le_antisymm
      · exact iSup_le fun A => iSup_le fun hA => iSup_le fun hAY a ha =>
          Subgroup.subset_closure ⟨A, hA, hAY, ha⟩
      · exact (Subgroup.closure_le N).2 hSN
    have hel : IsElemAbelian 2 N := by
      rw [hNS]
      refine B2F.isElemAbelian_closure (fun a ha b hb => ?_) (fun a ha => ?_)
      · have := hcomm b (hSN b hb) a (hNLb (hSN a ha))
        exact this.symm
      · obtain ⟨A, hA, hAY, haA⟩ := ha
        exact (hstab.2.1 A hA).2.2.1.2 a haA
    have hle : N ≤ pCoreOf 2 Y :=
      le_pCoreOf_of_le_normalizer 2 hNY hYnN (B2F.isPGroup_of_isElemAbelian hel)
    rw [pCoreOf_autI_eq_bot hV hred] at hle
    exact hNne (le_bot_iff.1 hle)
  refine quasithinGenFitting_eq_of_two_group_quot hLbN hNL ?_ ?_ hO2N
  · rcases autI_L_cases hV hred hLX hn hVL hLq with hq | h3
    · exact Or.inl (B1Red.isQuasisimple_to_open hq)
    · right
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact (IsPGroup.of_card (p := 3) (n := 1) (by rw [h3]; simp)).isNilpotent
  · intro y hy
    exact autI_exists_pow_mem hV hLX hn hT.1 hT.2.1 hLT y (hNY hy)

end Dichotomy

section Main

variable {X V L T R : Subgroup G}

theorem B2_10_2 (hV : IsElemAbelian 2 V) (hred : IsTwoReducedIn X V)
    (hQR : pCoreOf 2 X ≤ R) (hRT : R ≤ T) (hT : IsSylowTwoOf T X) (hLX : L ≤ X)
    (hn : X ≤ Subgroup.normalizer (L : Set G)) (hLT : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t)
    (hVL : ⁅V, L⁆ ≠ ⊥)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∨ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) :
    (IsSylowTwoOf (pCoreOf 2 (X ⊓ Subgroup.centralizer (V : Set G)))
        (X ⊓ Subgroup.centralizer (V : Set G)) ∧
      pCoreOf 2 X = R ⊓ Subgroup.centralizer (V : Set G)) ∧
    (CFSG.IsQuasisimple ↥(autI hV L) ∨ Nat.card ↥(autI hV L) = 3) ∧
    quasithinGenFitting (autI hV X) = autI hV L ∧
    (baum R = baum (pCoreOf 2 X) ∨
      (IsStableFF (autI hV X) (offenderImagesConjIn hV X R) ∧
        ffJP (offenderImagesConjIn hV X R) (autI hV X) ≤ ffJ (autI hV X) ∧
        quasithinGenFitting (ffJP (offenderImagesConjIn hV X R) (autI hV X)) = autI hV L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLqo : CFSG.Open.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∨
      Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := hLq.imp B1Red.isQuasisimple_to_open id
  have hTC := inf_centralizer_eq_pCoreOf hred hT hLX hn hLT hVL hLqo
  have hQC : pCoreOf 2 X ≤ Subgroup.centralizer (V : Set G) := pCoreOf_le_centralizer hred
  have hVR : V ≤ R := (le_pCoreOf_of_reduced hred).trans hQR
  have hRC : pCoreOf 2 X = R ⊓ Subgroup.centralizer (V : Set G) := by
    apply le_antisymm (le_inf hQR hQC)
    rw [← hTC]
    exact inf_le_inf_right _ hRT
  refine ⟨⟨?_, hRC⟩, autI_L_cases hV hred hLX hn hVL hLq,
    genFitting_autI_eq hV hred hT hLX hn hLT hVL hLq, ?_⟩
  ·
    set C := X ⊓ Subgroup.centralizer (V : Set G) with hC
    have hCX : C ≤ X := inf_le_left
    have hXC : X ≤ Subgroup.normalizer (C : Set G) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro c
      refine ⟨fun hc => ⟨X.mul_mem (X.mul_mem hx hc.1) (X.inv_mem hx),
        conj_mem_centralizer_of_le hred.2.1 hx hc.2⟩, fun hc => ?_⟩
      have h1 := conj_mem_centralizer_of_le hred.2.1 (X.inv_mem hx) hc.2
      refine ⟨?_, ?_⟩
      · have := X.mul_mem (X.mul_mem (X.inv_mem hx) hc.1) hx
        simpa [mul_assoc] using this
      · simpa [mul_assoc] using h1
    have hsyl : IsSylowTwoOf (T ⊓ C) C := A4.isSylowTwoOf_inf_normal hT hCX hXC
    have hD : T ⊓ C = pCoreOf 2 X := by
      rw [← hTC, hC, ← inf_assoc, inf_eq_left.2 hT.1]
    have hDC : pCoreOf 2 X ≤ C := le_inf ((pCoreOf_le 2 X)) hQC
    have hCn : C ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      hCX.trans (le_normalizer_pCoreOf 2 X)
    have hDO : pCoreOf 2 X ≤ pCoreOf 2 C :=
      le_pCoreOf_of_le_normalizer 2 hDC hCn (pCoreOf_isPGroup 2 X)
    refine ⟨pCoreOf_le 2 C, pCoreOf_isPGroup 2 C, ?_⟩
    intro h2
    have h1 : ((pCoreOf 2 X).subgroupOf C) ≤ ((pCoreOf 2 C).subgroupOf C) :=
      Subgroup.subgroupOf_mono C hDO
    rw [hD] at hsyl
    exact hsyl.2.2 (h2.trans (Subgroup.index_dvd_of_le h1))
  · by_cases hJ : thompsonJ R ≤ Subgroup.centralizer (V : Set G)
    · left
      have hJR : thompsonJ R ≤ R ⊓ Subgroup.centralizer (V : Set G) :=
        le_inf (thompsonJ_le_self R) hJ
      rw [hRC]
      exact baum_eq_baum_centralizer hV hVR hJR
    · right
      obtain ⟨hstab, hle⟩ := B2_10_1_stable_in hV hred.2.1 (hRT.trans hT.1) hVR hJ
      exact ⟨hstab, hle, genFitting_ffJP_eq hV hred hT hQR hRT hJ hLX hn hLT hVL hLq⟩

end Main

end CFSG.Quasithin.C124
