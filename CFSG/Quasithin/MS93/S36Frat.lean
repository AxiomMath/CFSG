module

public import CFSG.Quasithin.MS93.S32Cent
public import CFSG.Quasithin.MS93.Sec2Three
public import CFSG.LocalAnalysis.EvenBN.TwoF4.CoprimeProduct
public import CFSG.Quasithin.MS93.SkItems

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open scoped commutatorElement

variable {G : Type} [Group G]

namespace S36

section Burnside

variable [Finite G]

theorem commutator_mem_of_odd {P X : Subgroup G} (hP : IsPGroup 2 P) (hXP : X ≤ P)
    (hXn : P ≤ Subgroup.normalizer (X : Set G)) {l : G} (hlP : l ∈ Subgroup.normalizer (P : Set G))
    (hlX : l ∈ Subgroup.normalizer (X : Set G)) (hodd : Odd (orderOf l))
    (h : ⁅P, Subgroup.zpowers l⁆ ≤ frattiniIn P ⊔ X) {p : G} (hp : p ∈ P) :
    l * p * l⁻¹ * p⁻¹ ∈ X := by
  set A := Subgroup.zpowers l with hA
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := (Subgroup.zpowers_le).2 hlP
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := (Subgroup.zpowers_le).2 hlX
  have hcop : Nat.Coprime (Nat.card A) (Nat.card P) := by
    refine CFSG.LocalAnalysis.EvenBN.TwoF4.coprime_card_of_isPGroup Nat.prime_two hP ?_
    rw [hA, Nat.card_zpowers]
    exact Nat.odd_iff.mp hodd |> fun h2 => by omega
  have hsol := CFSG.LocalAnalysis.EvenBN.TwoF4.isSolvable_of_isPGroup Nat.prime_two hP
  have hcp := CFSG.LocalAnalysis.EvenBN.TwoF4.le_inf_centralizer_sup_commutator hAP hsol hcop
  set H := P ⊓ Subgroup.centralizer (A : Set G) ⊔ X with hH
  have hHP : H ≤ P := sup_le inf_le_left hXP
  have hPH : P ≤ H := by
    have h1 : P ≤ H ⊔ frattiniIn P := by
      refine hcp.trans (sup_le ?_ ?_)
      · exact le_sup_left.trans le_sup_left
      · refine h.trans (sup_le le_sup_right ?_)
        exact le_sup_right.trans le_sup_left
    have h2 : H.subgroupOf P ⊔ frattini ↥P = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : (x : G) ∈ H ⊔ frattiniIn P := h1 x.2
      have hmap : H ⊔ frattiniIn P = (H.subgroupOf P ⊔ frattini ↥P).map P.subtype := by
        rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hHP]
        rfl
      rw [hmap] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rw [← Subtype.ext hyx]
      exact hy
    have h3 := frattini_nongenerating h2
    intro x hx
    have : (⟨x, hx⟩ : ↥P) ∈ H.subgroupOf P := by rw [h3]; exact Subgroup.mem_top _
    exact this
  have hpH := hPH hp
  have hCX : P ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    inf_le_left.trans hXn
  rw [hH, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCX,
    Set.mem_mul] at hpH
  obtain ⟨c, hc, x, hx, rfl⟩ := hpH
  have hlc : l * c = c * l :=
    Subgroup.mem_centralizer_iff.mp (hc : c ∈ P ⊓ Subgroup.centralizer (A : Set G)).2 l
      (Subgroup.mem_zpowers l)
  have hlx : l * x * l⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hlX x).mp hx
  have hcX : c ∈ Subgroup.normalizer (X : Set G) := hCX hc
  have e : l * (c * x) * l⁻¹ * (c * x)⁻¹ = c * ((l * x * l⁻¹) * x⁻¹) * c⁻¹ := by
    calc l * (c * x) * l⁻¹ * (c * x)⁻¹ = (l * c) * x * l⁻¹ * x⁻¹ * c⁻¹ := by group
      _ = (c * l) * x * l⁻¹ * x⁻¹ * c⁻¹ := by rw [hlc]
      _ = c * ((l * x * l⁻¹) * x⁻¹) * c⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp hcX _).mp (X.mul_mem hlx (X.inv_mem hx))

theorem eq_top_of_perfect_of_pow_mem {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (D : Subgroup L) [D.Normal] (h2 : ∀ l : L, ∃ e : ℕ, l ^ 2 ^ e ∈ D) : D = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine QuotientGroup.subgroup_eq_top_of_subsingleton D ?_
  have hp : IsPGroup 2 (L ⧸ D) := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he⟩ := h2 l
    exact ⟨e, by rw [← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).mpr he]⟩
  rcases subsingleton_or_nontrivial (L ⧸ D) with hs | hs
  · exact hs
  · exact absurd hp.isNilpotent (Group.IsPerfect.not_isNilpotent (L ⧸ D))

theorem commutator_le_of_le_frattini_sup {P X L : Subgroup G} (hP : IsPGroup 2 P) (hXP : X ≤ P)
    (hXn : P ≤ Subgroup.normalizer (X : Set G)) (hLP : L ≤ Subgroup.normalizer (P : Set G))
    (hLX : L ≤ Subgroup.normalizer (X : Set G)) (hL : ⁅L, L⁆ = L)
    (h : ⁅P, L⁆ ≤ frattiniIn P ⊔ X) : ⁅P, L⁆ ≤ X := by
  have hconjX : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ x ∈ X, g * x * g⁻¹ ∈ X :=
    fun g hg x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hconjP : ∀ g ∈ L, ∀ p ∈ P, g * p * g⁻¹ ∈ P :=
    fun g hg p hp => (Subgroup.mem_normalizer_iff.mp (hLP hg) p).mp hp
  let D : Subgroup ↥L :=
    { carrier := {l | ∀ p ∈ P, (l : G) * p * (l : G)⁻¹ * p⁻¹ ∈ X}
      one_mem' := fun p _ => by simp
      mul_mem' := by
        intro l₁ l₂ h₁ h₂ p hp
        have e : ((l₁ * l₂ : ↥L) : G) * p * ((l₁ * l₂ : ↥L) : G)⁻¹ * p⁻¹ =
            (l₁ : G) * ((l₂ : G) * p * (l₂ : G)⁻¹ * p⁻¹) * (l₁ : G)⁻¹ *
              ((l₁ : G) * p * (l₁ : G)⁻¹ * p⁻¹) := by
          push_cast
          group
        rw [e]
        exact X.mul_mem (hconjX _ (hLX l₁.2) _ (h₂ p hp)) (h₁ p hp)
      inv_mem' := by
        intro l hl p hp
        have hp' : (l : G)⁻¹ * p * (l : G) ∈ P := by
          simpa using hconjP _ (L.inv_mem l.2) p hp
        have h1 := X.inv_mem (hl _ hp')
        have e : ((l⁻¹ : ↥L) : G) * p * ((l⁻¹ : ↥L) : G)⁻¹ * p⁻¹ =
            ((l : G) * ((l : G)⁻¹ * p * (l : G)) * (l : G)⁻¹ *
              ((l : G)⁻¹ * p * (l : G))⁻¹)⁻¹ := by
          push_cast
          group
        rw [e]
        exact h1 }
  have hDn : D.Normal := by
    refine ⟨fun l hl g p hp => ?_⟩
    have hp' : (g : G)⁻¹ * p * (g : G) ∈ P := by
      simpa using hconjP _ (L.inv_mem g.2) p hp
    have e : ((g * l * g⁻¹ : ↥L) : G) * p * ((g * l * g⁻¹ : ↥L) : G)⁻¹ * p⁻¹ =
        (g : G) * ((l : G) * ((g : G)⁻¹ * p * (g : G)) * (l : G)⁻¹ *
          ((g : G)⁻¹ * p * (g : G))⁻¹) * (g : G)⁻¹ := by
      push_cast
      group
    rw [e]
    exact hconjX _ (hLX g.2) _ (hl _ hp')
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  have hDtop : D = ⊤ := by
    refine eq_top_of_perfect_of_pow_mem D fun l => ?_
    obtain ⟨e, m, hm, hlm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos l).ne'
    refine ⟨e, fun p hp => ?_⟩
    have hord : orderOf ((l : G) ^ 2 ^ e) = m := by
      have h1 : ((l ^ 2 ^ e : ↥L) : G) = (l : G) ^ 2 ^ e := by push_cast; rfl
      rw [← h1, Subgroup.orderOf_coe,
        orderOf_pow_of_dvd (by positivity) (by rw [hlm]; exact Dvd.intro m rfl), hlm,
        Nat.mul_div_cancel_left _ (by positivity)]
    have hlP : (l : G) ^ 2 ^ e ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.pow_mem _ (hLP l.2) _
    have hlX : (l : G) ^ 2 ^ e ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.pow_mem _ (hLX l.2) _
    have hle : ⁅P, Subgroup.zpowers ((l : G) ^ 2 ^ e)⁆ ≤ frattiniIn P ⊔ X :=
      (Subgroup.commutator_mono le_rfl
        ((Subgroup.zpowers_le).2 (L.pow_mem l.2 _))).trans h
    have := commutator_mem_of_odd hP hXP hXn hlP hlX (by rw [hord]; exact hm) hle hp
    simpa using this
  rw [Subgroup.commutator_le]
  intro p hp l hl
  have hlD : (⟨l, hl⟩ : ↥L) ∈ D := by rw [hDtop]; exact Subgroup.mem_top _
  have h1 : l * p⁻¹ * l⁻¹ * p⁻¹⁻¹ ∈ X := hlD _ (P.inv_mem hp)
  rw [inv_inv] at h1
  have e : ⁅p, l⁆ = p * (l * p⁻¹ * l⁻¹ * p) * p⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact hconjX _ (hXn hp) _ h1

end Burnside

section Generation

variable [Finite G] {M T L : Subgroup G}

theorem le_normalClosureIn_of_not_le (h : PUHyp M T L) {Y : Subgroup G} (hYT : Y ≤ T)
    (hYQ : ¬ Y ≤ pCoreOf 2 M) : L ≤ normalClosureIn M Y := by
  by_contra hL
  set Q := pCoreOf 2 M with hQ
  set N := normalClosureIn M Y with hN
  have hNM : N ≤ M := normalClosureIn_le M Y
  have hNn : M ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).1 (normalClosureIn_normal M Y)
  have hNL : ⁅N, L⁆ ≤ Q := h.commutator_le_pCoreOf_M hNM hNn hL
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf M
  have hconjQ : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q :=
    fun g hg q hq => (Subgroup.mem_normalizer_iff.mp (hQn hg) q).mp hq
  let K : Subgroup G :=
    { carrier := {x | x ∈ M ∧ ∀ g ∈ L, g * x * g⁻¹ * x⁻¹ ∈ Q}
      one_mem' := ⟨M.one_mem, fun g _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
        refine ⟨M.mul_mem hxM hyM, fun g hg => ?_⟩
        have e : g * (x * y) * g⁻¹ * (x * y)⁻¹ =
            (g * x * g⁻¹ * x⁻¹) * (x * (g * y * g⁻¹ * y⁻¹) * x⁻¹) := by group
        rw [e]
        exact Q.mul_mem (hx g hg) (hconjQ x hxM _ (hy g hg))
      inv_mem' := by
        rintro x ⟨hxM, hx⟩
        refine ⟨M.inv_mem hxM, fun g hg => ?_⟩
        have e : g * x⁻¹ * g⁻¹ * x⁻¹⁻¹ = x⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
        rw [e]
        exact hconjQ _ (M.inv_mem hxM) _ (Q.inv_mem (hx g hg)) }
  have hNK : N ≤ K := fun n hn => ⟨hNM hn, fun g hg => by
    have := Subgroup.commutator_mem_commutator hg hn
    rw [Subgroup.commutator_comm] at this
    simpa [commutatorElement_def] using hNL this⟩
  have hQK : Q ≤ K := fun q hq => ⟨pCoreOf_le' M hq, fun g hg =>
    Q.mul_mem (hconjQ g (h.L_le hg) q hq) (Q.inv_mem hq)⟩
  set C := (N ⊔ Q) ⊓ T with hC
  have hCM : C ≤ M := inf_le_right.trans h.le
  have hNQn : M ≤ Subgroup.normalizer ((N ⊔ Q : Subgroup G) : Set G) :=
    le_normalizer_sup hNn hQn
  have hTn : T ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_inf (h.le.trans hNQn) Subgroup.le_normalizer
  have key : ∀ g ∈ L, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hNQn (h.L_le hg)) c).mp hc.1, ?_⟩
    have hcK : c ∈ K := sup_le hNK hQK hc.1
    have e : g * c * g⁻¹ = (g * c * g⁻¹ * c⁻¹) * c := by group
    rw [e]
    exact T.mul_mem (h.pCore_le (hcK.2 g hg)) hc.2
  have hLn : L ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨key g hg c, fun hc' => ?_⟩
    have := key g⁻¹ (L.inv_mem hg) _ hc'
    simpa [mul_assoc] using this
  have hMn : M ≤ Subgroup.normalizer (C : Set G) := by
    rw [h.eq_sup]
    exact sup_le hLn hTn
  have hCQ : C ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCM hMn
    (h.isPGroup.to_le inf_le_right)
  exact hYQ fun y hy =>
    hCQ ⟨le_sup_left (a := N) (b := Q) (le_normalClosureIn (hYT.trans h.le) hy), hYT hy⟩

end Generation

section Frattini

theorem commutator_le_frattiniIn [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) :
    ⁅P, P⁆ ≤ frattiniIn P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥P) := ⟨hP⟩
  have h1 := CFSG.commutator_le_frattini_of_isPGroup (R := ↥P) (p := 2)
  have h2 := Subgroup.map_mono (f := P.subtype) h1
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h2
  exact h2

theorem le_normalizer_frattiniIn {M P : Subgroup G}
    (hP : M ≤ Subgroup.normalizer (P : Set G)) :
    M ≤ Subgroup.normalizer (frattiniIn P : Set G) := by
  have key : ∀ m ∈ M, ∀ x ∈ frattiniIn P, m * x * m⁻¹ ∈ frattiniIn P := by
    intro m hm x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmP : ∀ z : ↥P, m * (z : G) * m⁻¹ ∈ P := fun z =>
      (Subgroup.mem_normalizer_iff.1 (hP hm) z).1 z.2
    have hmP' : ∀ z : ↥P, m⁻¹ * (z : G) * m⁻¹⁻¹ ∈ P := fun z =>
      (Subgroup.mem_normalizer_iff.1 (hP (M.inv_mem hm)) z).1 z.2
    let σ : ↥P ≃* ↥P :=
      { toFun := fun z => ⟨m * z * m⁻¹, hmP z⟩
        invFun := fun z => ⟨m⁻¹ * z * m⁻¹⁻¹, hmP' z⟩
        left_inv := fun z => Subtype.ext (by simp [mul_assoc])
        right_inv := fun z => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun z w => Subtype.ext (by simp [mul_assoc]) }
    have hσ : (frattini ↥P).map σ.toMonoidHom = frattini ↥P :=
      (Subgroup.characteristic_iff_map_eq.mp (frattini_characteristic)) σ
    have hmem : σ y ∈ frattini ↥P := by
      rw [← hσ]
      exact ⟨y, hy, rfl⟩
    exact ⟨σ y, hmem, rfl⟩
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key m hm x, fun hx => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) _ hx
  simpa [mul_assoc] using this

theorem frattiniIn_le (P : Subgroup G) : frattiniIn P ≤ P := Subgroup.map_subtype_le _

end Frattini

section TImage

variable {M T : Subgroup G}

@[expose] def tImage (ψ : MulAut ↥T) (K : Subgroup G) : Subgroup G :=
  ((K.subgroupOf T).map ψ.toMonoidHom).map T.subtype

theorem tImage_le (ψ : MulAut ↥T) (K : Subgroup G) : tImage ψ K ≤ T :=
  Subgroup.map_subtype_le _

theorem tImage_subgroupOf (ψ : MulAut ↥T) (K : Subgroup G) :
    (tImage ψ K).subgroupOf T = (K.subgroupOf T).map ψ.toMonoidHom :=
  Subgroup.comap_map_eq_self_of_injective T.subtype_injective _

variable (hTM : T ≤ M)

theorem imM_map_conj_inr (ψ : MulAut ↥T) {K : Subgroup G} (hK : K ≤ T) :
    (imM hTM K).map
        (MulAut.conj ((puAmalgam hTM).ofB (SemidirectProduct.inr ψ))).toMonoidHom =
      imM hTM (tImage ψ K) := by
  rw [imM_of_le hTM hK, imM_of_le hTM (tImage_le ψ K), tImage_subgroupOf, Subgroup.map_map,
    Subgroup.map_map]
  congr 1
  ext t
  simp only [MonoidHom.coe_comp, Function.comp_apply, puAmalgam.ofT, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, ← map_inv, ← map_mul]
  rw [← SemidirectProduct.inl_aut]
  rfl

end TImage

section Step2

variable [Finite G] {M T L : Subgroup G}

theorem vq_eq_uq_of_commutator_le (h : PUHyp M T L) (hXL : ⁅Xq M, L⁆ ≤ Uq M T L)
    {Y : Subgroup G} (hYT : Y ≤ T) (hYQ : ¬ Y ≤ pCoreOf 2 M)
    (hle : ⁅Y, pCoreOf 2 M⁆ ≤ Xq M ⊔ frattiniIn (pCoreOf 2 M)) : Vq M L = Uq M T L := by
  set Q := pCoreOf 2 M with hQ
  set W := Xq M ⊔ frattiniIn Q with hW
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf M
  have hWn : M ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_sup (le_normalizer_Xq M) (le_normalizer_frattiniIn hQn)
  have hconjQ : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q :=
    fun g hg q hq => (Subgroup.mem_normalizer_iff.mp (hQn hg) q).mp hq
  have hconjW : ∀ g ∈ M, ∀ w ∈ W, g * w * g⁻¹ ∈ W :=
    fun g hg w hw => (Subgroup.mem_normalizer_iff.mp (hWn hg) w).mp hw
  let K : Subgroup G :=
    { carrier := {x | x ∈ M ∧ ∀ q ∈ Q, q * x * q⁻¹ * x⁻¹ ∈ W}
      one_mem' := ⟨M.one_mem, fun q _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
        refine ⟨M.mul_mem hxM hyM, fun q hq => ?_⟩
        have e : q * (x * y) * q⁻¹ * (x * y)⁻¹ =
            (q * x * q⁻¹ * x⁻¹) * (x * (q * y * q⁻¹ * y⁻¹) * x⁻¹) := by group
        rw [e]
        exact W.mul_mem (hx q hq) (hconjW x hxM _ (hy q hq))
      inv_mem' := by
        rintro x ⟨hxM, hx⟩
        refine ⟨M.inv_mem hxM, fun q hq => ?_⟩
        have e : q * x⁻¹ * q⁻¹ * x⁻¹⁻¹ = x⁻¹ * (q * x * q⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
        rw [e]
        exact hconjW _ (M.inv_mem hxM) _ (W.inv_mem (hx q hq)) }
  have hKM : K ≤ M := fun x hx => hx.1
  have hKconj : ∀ m ∈ M, ∀ x ∈ K, m * x * m⁻¹ ∈ K := by
    rintro m hm x ⟨hxM, hx⟩
    refine ⟨M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm), fun q hq => ?_⟩
    have hq' : m⁻¹ * q * m ∈ Q := by
      simpa using hconjQ _ (M.inv_mem hm) q hq
    have e : q * (m * x * m⁻¹) * q⁻¹ * (m * x * m⁻¹)⁻¹ =
        m * ((m⁻¹ * q * m) * x * (m⁻¹ * q * m)⁻¹ * x⁻¹) * m⁻¹ := by group
    rw [e]
    exact hconjW _ hm _ (hx _ hq')
  have hKn : (K.subgroupOf M).Normal := by
    refine ⟨fun x hx m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hKconj m m.2 x hx
  have hYK : Y ⊓ M ≤ K := by
    rintro y ⟨hy, hyM⟩
    refine ⟨hyM, fun q hq => ?_⟩
    have := Subgroup.commutator_mem_commutator hq hy
    rw [Subgroup.commutator_comm] at this
    simpa [commutatorElement_def] using hle this
  have hNK : normalClosureIn M Y ≤ K := normalClosureIn_le_of hKM hKn hYK
  have hLK : L ≤ K := (le_normalClosureIn_of_not_le h hYT hYQ).trans hNK
  have hQL : ⁅Q, L⁆ ≤ frattiniIn Q ⊔ Xq M := by
    rw [sup_comm]
    rw [Subgroup.commutator_le]
    intro q hq l hl
    simpa [commutatorElement_def] using (hLK hl).2 q hq
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hQX : ⁅Q, L⁆ ≤ Xq M :=
    commutator_le_of_le_frattini_sup hQ2 (Xq_le_pCoreOf M)
      ((pCoreOf_le' M).trans (le_normalizer_Xq M)) (h.L_le.trans hQn)
      (h.L_le.trans (le_normalizer_Xq M)) h.perfect hQL
  have hV : Vq M L = ⁅⁅Q, L⁆, L⁆ :=
    commutator_eq_commutator_commutator (pCoreOf_le' M) h.L_le hQn h.le_normalizer h.perfect
  refine le_antisymm ?_ (Subgroup.commutator_mono h.Z0q_le_pCoreOf le_rfl)
  rw [hV]
  exact (Subgroup.commutator_mono hQX le_rfl).trans hXL

theorem zm_inr (h : PUHyp M T L) (ψ : MulAut ↥T) :
    ZM (puAmalgam h.le) ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _) =
      imM h.le (tImage ψ (Z0q M T)) := by
  rw [zm_smul, puAmalgam.zm_baseA, imM_map_conj_inr h.le ψ (h.Z0q_le_pCoreOf.trans h.pCore_le)]

theorem xm_baseA (h : PUHyp M T L) :
    XM (puAmalgam h.le) (baseA _) = imM h.le (Xq M) := by
  rw [puAmalgam.xm_baseA, h.normalCoreIn_eq]

theorem s33Hyp_Q_inr (h : PUHyp M T L) (hXL : ⁅Xq M, L⁆ ≤ Uq M T L)
    (hV : Vq M L ≠ Uq M T L) (ψ : MulAut ↥T)
    (hc : IsCritical (puAmalgam h.le) (baseA _)
      ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _)) :
    ¬ ⁅ZM (puAmalgam h.le) ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _),
          Qv (puAmalgam h.le) (baseA _)⁆ ≤
        ⁅XM (puAmalgam h.le) (baseA _),
            XM (puAmalgam h.le) ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _)⁆ ⊔
          ⁅critA (puAmalgam h.le) (baseA _)
              ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _),
            Qv (puAmalgam h.le) (baseA _)⁆ := by
  intro H
  set X := puAmalgam h.le with hX
  set α'' := X.ofB (SemidirectProduct.inr ψ) • baseA X with hα''
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hQα : Qv X (baseA X) = imM h.le (pCoreOf 2 M) :=
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  have hc' : IsCritical X α'' (baseA X) := ms22_iii X h20 hb0 hC hc
  have hXst : XM X α'' ≤ stab X (baseA X) := xm_le_stab_of_isCritical X h20 hb0 hC hc'
  have hZT : tImage ψ (Z0q M T) ≤ M := (tImage_le ψ _).trans h.le
  have hYQ : ¬ tImage ψ (Z0q M T) ≤ pCoreOf 2 M := fun hle =>
    hc'.2.2 (by rw [zm_inr h, hQα]; exact imM_mono h.le hle)
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have key : ⁅tImage ψ (Z0q M T), pCoreOf 2 M⁆ ≤ Xq M ⊔ frattiniIn (pCoreOf 2 M) := by
    rw [← imM_le_imM_iff h.le (commutator_le_of_le hZT (pCoreOf_le' M)),
      imM_commutator h.le hZT (pCoreOf_le' M), ← zm_inr h, ← hQα]
    refine H.trans (sup_le ?_ ?_)
    · refine (commutator_le_left_of_le_normalizer
        (hXst.trans (stab_le_normalizer_xm X _))).trans ?_
      rw [xm_baseA h]
      exact imM_mono h.le le_sup_left
    · calc ⁅critA X (baseA X) α'', Qv X (baseA X)⁆ ≤ ⁅Qv X (baseA X), Qv X (baseA X)⁆ :=
            Subgroup.commutator_mono inf_le_right le_rfl
        _ = imM h.le ⁅pCoreOf 2 M, pCoreOf 2 M⁆ := by
            rw [hQα, imM_commutator h.le (pCoreOf_le' M) (pCoreOf_le' M)]
        _ ≤ imM h.le (Xq M ⊔ frattiniIn (pCoreOf 2 M)) :=
            imM_mono h.le ((commutator_le_frattiniIn hQ2).trans le_sup_right)
  exact hV (vq_eq_uq_of_commutator_le h hXL (tImage_le ψ _) hYQ key)

end Step2

end S36

open S36

section Step2

variable [Finite G] {M T L : Subgroup G}

theorem s33Hyp_Q_of_ne (h : PUHyp M T L) (hXL : ⁅Xq M, L⁆ ≤ Uq M T L)
    (hb : critDist (puAmalgam h.le) = 2) (hV : Vq M L ≠ Uq M T L) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) α') :
    Qv (puAmalgam h.le) (baseA _) ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' (baseA _) 1) ∧
    Qv (puAmalgam h.le) (baseA _) ≤
      Subgroup.centralizer (critR (puAmalgam h.le) (baseA _) α' : Set (puAmalgam h.le).Universal) ∧
    ¬ ⁅ZM (puAmalgam h.le) α', Qv (puAmalgam h.le) (baseA _)⁆ ≤
        ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
          ⁅critA (puAmalgam h.le) (baseA _) α', Qv (puAmalgam h.le) (baseA _)⁆ := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 2 := hc.2.1.trans hb
  have hadj1 : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo (puAmalgam h.le) (baseA _) α' 1) :=
    adj_geo_one _ (by omega)
  have hgeo : geo (puAmalgam h.le) α' (baseA _) 1 = geo (puAmalgam h.le) (baseA _) α' 1 := by
    have := geo_symm (puAmalgam h.le) (u := baseA _) (w := α') (i := 1) (by omega)
    rwa [hd] at this
  have hc' : IsCritical (puAmalgam h.le) α' (baseA _) := ms22_iii _ h20 hb0 hC hc
  refine ⟨?_, ?_, ?_⟩
  · rw [hgeo]
    exact qv_le_qv _ h20 (isMVtx_baseA _) hadj1
  · have hZst : ZM (puAmalgam h.le) α' ≤ stab (puAmalgam h.le) (baseA _) := by
      exact (zm_le_qv_geo_one _ h20 hb0 hc).trans (qv_le_stab_of_adj _ hadj1.symm)
    have hR : critR (puAmalgam h.le) (baseA _) α' ≤ ZM (puAmalgam h.le) (baseA _) :=
      commutator_le_left_of_le_normalizer (hZst.trans (stab_le_normalizer_zm _ _))
    have hQZ : Qv (puAmalgam h.le) (baseA _) ≤
        Subgroup.centralizer (ZM (puAmalgam h.le) (baseA _) : Set (puAmalgam h.le).Universal) := by
      rw [← Subgroup.le_centralizer_iff, ← Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact (ms21_iv _ h20 (isMVtx_baseA _)).1
    exact hQZ.trans (Subgroup.centralizer_le hR)
  · obtain ⟨g, hg, hgβ⟩ := exists_mem_stab_smul _ hadj1 (adj_baseA_baseB (puAmalgam h.le))
    have hg' : g • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).mp hg
    have hc'' : IsCritical (puAmalgam h.le) (baseA _) (g • α') := by
      have := (isCritical_smul _ g (baseA _) α').mpr hc
      rwa [hg'] at this
    have hgeo'' : geo (puAmalgam h.le) (baseA _) (g • α') 1 = baseB _ := by
      have := geo_smul (puAmalgam h.le) g (baseA _) α' 1
      rwa [hg', hgβ] at this
    have hd'' : (puAmalgam h.le).treeGraph.dist (baseA _) (g • α') = 2 := hc''.2.1.trans hb
    have hadjB : (puAmalgam h.le).treeGraph.Adj (baseB _) (g • α') := by
      have := adj_geo (puAmalgam h.le) (u := baseA _) (w := g • α') (i := 1) (by omega)
      rwa [hgeo'', geo_of_le _ (by omega)] at this
    obtain ⟨ψ, hψ⟩ := (puAmalgam.adj_baseB_iff_mulAut h.le (g • α')).mp hadjB
    have H'' := s33Hyp_Q_inr h hXL hV ψ (hψ ▸ hc'')
    rw [← hψ] at H''
    intro H
    apply H''
    have hmap := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) H
    have hQ : (Qv (puAmalgam h.le) (baseA _)).map (MulAut.conj g).toMonoidHom =
        Qv (puAmalgam h.le) (baseA _) := by
      rw [← qv_smul, hg']
    have hXα : (XM (puAmalgam h.le) (baseA _)).map (MulAut.conj g).toMonoidHom =
        XM (puAmalgam h.le) (baseA _) := by
      rw [← xm_smul, hg']
    have hA : (critA (puAmalgam h.le) (baseA _) α').map (MulAut.conj g).toMonoidHom =
        critA (puAmalgam h.le) (baseA _) (g • α') := by
      rw [critA, critA, Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← xm_smul, hQ]
    rw [Subgroup.map_commutator, Subgroup.map_sup, Subgroup.map_commutator,
      Subgroup.map_commutator, ← zm_smul, hQ, hXα, ← xm_smul, hA] at hmap
    exact hmap

end Step2

end CFSG.Quasithin.MS93
