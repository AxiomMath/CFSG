module

public import CFSG.Quasithin.H13.A6S13833b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

@[expose] def NatLineAt (a b : Fin 6 → ZMod 2) : Prop :=
  ∑ i, a i = 0 → ∑ i, b i = 0 → ¬ (a = 0 ∨ a = onesV) → ¬ (b = 0 ∨ b = onesV) →
    ¬ (b = a ∨ b = a + onesV) →
    (∀ σ ∈ cList, Perm.sign σ = 1 → InLn a b (vp σ a) ∧ InLn a b (vp σ b)) →
    InLn e01 e23 a ∧ InLn e01 e23 b

instance (a b : Fin 6 → ZMod 2) : Decidable (NatLineAt a b) := by
  unfold NatLineAt; infer_instance

theorem nat_line_cA6 : ∀ a b : Fin 6 → ZMod 2, NatLineAt a b := by
  decide +kernel

@[expose] def dotv (a b : Fin 6 → ZMod 2) : ZMod 2 := ∑ i, a i * b i

@[expose] def PerpAt (q : Fin 6 → ZMod 2) (σ : Perm (Fin 6)) : Prop :=
  InLn e01 e23 q → ¬ (q = 0 ∨ q = onesV) → (vp σ q = q ∨ vp σ q = q + onesV) →
    ∀ w ∈ [e01, e23, e01 + e23], dotv (vp σ w) q = 0

instance (q : Fin 6 → ZMod 2) (σ : Perm (Fin 6)) : Decidable (PerpAt q σ) := by
  unfold PerpAt; infer_instance

theorem perpAt_all : ∀ q : Fin 6 → ZMod 2, ∀ σ : Perm (Fin 6), PerpAt q σ := by
  decide +kernel

@[expose] def c3Out : List (Perm (Fin 6)) :=
  [swap 2 3 * swap 3 4, swap 0 1 * swap 1 4, swap 0 1 * swap 1 2]

@[expose] def OutAt (q : Fin 6 → ZMod 2) : Prop :=
  InLn e01 e23 q → ¬ (q = 0 ∨ q = onesV) →
    ∃ σ ∈ c3Out, (vp σ q = q ∨ vp σ q = q + onesV) ∧ σ * iota0 ≠ iota0 * σ

instance (q : Fin 6 → ZMod 2) : Decidable (OutAt q) := by unfold OutAt; infer_instance

theorem outAt_all : ∀ q : Fin 6 → ZMod 2, OutAt q := by decide +kernel

theorem c3Out_facts : ∀ σ ∈ c3Out, Perm.sign σ = 1 ∧ σ ^ 3 = 1 ∧ σ ≠ 1 := by decide +kernel

@[expose] def StabW3e (σ : Perm (Fin 6)) : Prop :=
  (∀ y : P6, InW4 y → InW3 y → InW3 (act4f σ y)) → act4f σ e0123 = e0123

instance (σ : Perm (Fin 6)) : Decidable (StabW3e σ) := by unfold StabW3e; infer_instance

theorem stabW3e_all : ∀ σ : Perm (Fin 6), StabW3e σ := by decide +kernel

@[expose] def NonPerpAt (q : Fin 6 → ZMod 2) : Prop :=
  ∑ i, q i = 0 → ¬ (q = 0 ∨ q = onesV) →
    ∃ w ∈ [e01, e01 + e23 + Pi.single 1 1 + Pi.single 2 1, Pi.single 0 1 + Pi.single 3 1,
      Pi.single 0 1 + Pi.single 4 1, Pi.single 0 1 + Pi.single 5 1], ∑ i, w i = 0 ∧ dotv w q = 1

instance (q : Fin 6 → ZMod 2) : Decidable (NonPerpAt q) := by unfold NonPerpAt; infer_instance

theorem nonPerpAt_all : ∀ q : Fin 6 → ZMod 2, NonPerpAt q := by decide +kernel

theorem dotv_add (a b c : Fin 6 → ZMod 2) : dotv (a + b) c = dotv a c + dotv b c := by
  unfold dotv
  rw [← Finset.sum_add_distrib]
  congr 1
  funext i
  simp only [Pi.add_apply]
  ring

theorem dotv_zero (c : Fin 6 → ZMod 2) : dotv 0 c = 0 := by
  unfold dotv; simp

theorem dotv_ones (c : Fin 6 → ZMod 2) : dotv onesV c = ∑ i, c i := by
  unfold dotv; simp

theorem dotv_vp (σ : Perm (Fin 6)) (v w : Fin 6 → ZMod 2) :
    dotv (vp σ v) (vp σ w) = dotv v w := by
  unfold dotv vp
  exact Equiv.sum_comp σ⁻¹ (fun i => v i * w i)

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

section NatLine

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (AltHeart 6)}
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
      (QuotientAddGroup.mk (permWeight 6 (ρ h) x) : AltHeart 6) = Multiplicative.toAdd (β v))
  {τ : Perm (Fin 6)} {ρ' : ↥S.G1 →* Perm (Fin 6)} (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
  (hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  {K : Subgroup G}
  (honto' : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ' k = σ)
include hβk hβe hρ' hN' honto'

theorem nat_V3_line {v : G} (hv : v ∈ S.V3) (r : ↥(evenWeight 6))
    (hr : (QuotientAddGroup.mk r : AltHeart 6) = Multiplicative.toAdd (β ⟨v, S.V3_le_UH hv⟩)) :
    InLn e01 e23 (vp τ⁻¹ (r : Fin 6 → ZMod 2)) := by
  obtain ⟨ra, hra, -⟩ :=
    exists_rep5 (Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩))
  obtain ⟨rb, hrb, -⟩ :=
    exists_rep5 (Multiplicative.toAdd (β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩))
  have hstab := S.mem_stabSubN_iff hβk hβe hra hrb
  set a := vp τ⁻¹ (ra : Fin 6 → ZMod 2) with ha
  set b := vp τ⁻¹ (rb : Fin 6 → ZMod 2) with hb
  have hinv : ∀ σ ∈ cList, Perm.sign σ = 1 → InLn a b (vp σ a) ∧ InLn a b (vp σ b) := by
    intro σ hσ hs
    obtain ⟨k, -, hk⟩ := honto' σ (Perm.mem_alternatingGroup.mpr hs)
    have hkN : (k : G) ∈ Subgroup.normalizer (S.V3 : Set G) := (hN' k).1 (by rw [hk]; exact hσ)
    have hst : StabLn (ra : Fin 6 → ZMod 2) rb (ρ k) := (hstab k).2 hkN
    have hρk : ρ k = τ * σ * τ⁻¹ := by rw [← hk, hρ']; group
    have key : ∀ w : Fin 6 → ZMod 2, InLn (ra : Fin 6 → ZMod 2) rb (vp (ρ k) w) →
        InLn a b (vp σ (vp τ⁻¹ w)) := by
      intro w hw
      have h1 : vp σ (vp τ⁻¹ w) = vp τ⁻¹ (vp (ρ k) w) := by
        rw [hρk, ← vp_mul, ← vp_mul]; congr 1; group
      rw [h1]
      refine inLn_maps (vp_add τ⁻¹) (vp_const τ⁻¹) (Or.inl (Or.inr (Or.inl rfl)))
        (Or.inl (Or.inr (Or.inr (Or.inl rfl)))) hw
    exact ⟨key _ hst.1, key _ hst.2⟩
  have hne : ∀ (u : G) (hu : u ∈ S.V3), u ∉ fsuV1 T V → ∀ x : ↥(evenWeight 6),
      (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β ⟨u, S.V3_le_UH hu⟩) →
      ¬ ((x : Fin 6 → ZMod 2) = 0 ∨ (x : Fin 6 → ZMod 2) = onesV) := by
    intro u hu hn x hx h
    apply hn
    refine (hβk ⟨u, S.V3_le_UH hu⟩).1 (Multiplicative.toAdd.injective ?_)
    rw [toAdd_one, ← hx]
    exact (mk_eq_zero_iff x).2 h
  have hτ0 : ∀ w : Fin 6 → ZMod 2, ¬ (w = 0 ∨ w = onesV) → ¬ (vp τ⁻¹ w = 0 ∨ vp τ⁻¹ w = onesV) := by
    intro w hw h
    apply hw
    rcases h with h | h
    · left; exact vp_injective τ⁻¹ (by rw [h, vp_zero])
    · right; exact vp_injective τ⁻¹ (by rw [h]; exact (vp_const τ⁻¹).symm)
  have ha0 := hτ0 _ (hne _ S.u1_mem_V3 S.u1_not_V1 ra hra)
  have hb0 := hτ0 _ (hne _ S.u2_mem_V3 S.u2_not_V1 rb hrb)
  have hab : ¬ (b = a ∨ b = a + onesV) := by
    intro h
    have h12 : S.u2 * S.u1⁻¹ ∈ S.V3 := S.V3.mul_mem S.u2_mem_V3 (S.V3.inv_mem S.u1_mem_V3)
    apply hne _ h12 S.u21_not_V1 (rb - ra) ?_
    · have e : (((rb - ra : ↥(evenWeight 6)) : Fin 6 → ZMod 2)) = vp τ (b + a) := by
        simp only [AddSubgroup.coe_sub, hb, ha, vp_add, vp_vp_inv]
        rw [sub_eq_add_neg]
        congr 1
        funext i
        simp
      rw [e]
      rcases h with h | h
      · left; rw [h, vadd_self, vp_zero]
      · right; rw [h, add_comm, ← add_assoc, vadd_self, zero_add]; exact vp_const τ
    · have e : β ⟨S.u2 * S.u1⁻¹, S.V3_le_UH h12⟩ =
          β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩ * (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩)⁻¹ := by
        rw [← map_inv, ← map_mul]; rfl
      rw [e, toAdd_mul, toAdd_inv, ← hra, ← hrb, QuotientAddGroup.mk_sub, sub_eq_add_neg]
  have hsa : ∑ i, a i = 0 := by rw [ha, sum_vp]; exact sum_eq_zero ra
  have hsb : ∑ i, b i = 0 := by rw [hb, sum_vp]; exact sum_eq_zero rb
  obtain ⟨hla, hlb⟩ := nat_line_cA6 a b hsa hsb ha0 hb0 hab hinv
  have hl := S.inLn_of_V3 hβk hra hrb hv r hr
  exact inLn_maps (vp_add τ⁻¹) (vp_const τ⁻¹) hla hlb hl

end NatLine

end Setting4

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

@[expose] noncomputable def K2 : Subgroup G := oTwoRes (Subgroup.centralizer (S.V2 : Set G))

@[expose] noncomputable def U2 : Subgroup G := conjClosure V S.K2

@[expose] noncomputable def U21 : Subgroup G := conjClosure S.V3 S.K2

include S

theorem K2_le_centralizer : S.K2 ≤ Subgroup.centralizer (S.V2 : Set G) := oTwoRes_le _

theorem K2_le_G1 : S.K2 ≤ S.G1 := by
  intro k hk
  have hz : S.z ∈ S.V2 := S.V1_le_V2 ((S.mem_V1_iff).2 (Or.inr rfl))
  show k ∈ Subgroup.centralizer ({S.z} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (S.K2_le_centralizer hk) S.z hz).symm

theorem normalizer_V2_le_normalizer_centralizer :
    Subgroup.normalizer (S.V2 : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (S.V2 : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : g⁻¹ * v * g ∈ S.V2 := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) v).mp hv
      simpa using this
    have h := hc _ hv'
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * v := by group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : g * v * g⁻¹ ∈ S.V2 := (Subgroup.mem_normalizer_iff.mp hg v).mp hv
    have h := hc _ hv'
    calc v * c = g⁻¹ * ((g * v * g⁻¹) * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * (g * v * g⁻¹)) * g := by rw [h]
      _ = c * v := by group

theorem normalizer_V2_le_normalizer_K2 :
    Subgroup.normalizer (S.V2 : Set G) ≤ Subgroup.normalizer (S.K2 : Set G) :=
  A5.le_normalizer_oTwoRes_of_le_normalizer S.normalizer_V2_le_normalizer_centralizer

theorem K2_le_normalizer_V2 : S.K2 ≤ Subgroup.normalizer (S.V2 : Set G) :=
  S.K2_le_centralizer.trans (Subgroup.centralizer_le_normalizer _)

theorem U21_le_U2 : S.U21 ≤ S.U2 := conjClosure_mono S.V3_le_V le_rfl

theorem V_le_U2 : V ≤ S.U2 := le_conjClosure V S.K2

theorem V3_le_U21 : S.V3 ≤ S.U21 := le_conjClosure S.V3 S.K2

theorem U21_le_UH : S.U21 ≤ conjClosure S.V3 S.G1 := conjClosure_mono le_rfl S.K2_le_G1

theorem U2_le_VH : S.U2 ≤ conjClosure V S.G1 := conjClosure_mono le_rfl S.K2_le_G1

theorem normalizes_conjClosure_K2 {X : Subgroup G} {g : G}
    (hg2 : g ∈ Subgroup.normalizer (S.V2 : Set G)) (hgX : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (conjClosure X S.K2 : Set G) := by
  have hK := S.normalizer_V2_le_normalizer_K2 hg2
  have e : conjSub g (conjClosure X S.K2) = conjClosure X S.K2 := by
    rw [conjSub_conjClosure_eq, F7.conjSub_eq_of_mem_normalizer hgX,
      F7.conjSub_eq_of_mem_normalizer hK]
  refine F7.mem_normalizer_of_conj_le e.le ?_
  rw [← e, conjSub_conjSub_inv, e]

theorem normalizes_U2 {g : G} (hg2 : g ∈ Subgroup.normalizer (S.V2 : Set G))
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) :
    g ∈ Subgroup.normalizer (S.U2 : Set G) :=
  S.normalizes_conjClosure_K2 hg2 hgV

section NatPerp

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

theorem card_U21_le_nat : Nat.card S.U21 ≤ 16 := by
  obtain ⟨r₂, hr₂, -⟩ :=
    exists_rep5 (Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩))
  set q := vp τ⁻¹ (r₂ : Fin 6 → ZMod 2) with hq
  have hql := S.nat_V3_line hβk hβe hρ' hN' honto' S.u1_mem_V3 r₂ hr₂
  have hqs : ∑ i, q i = 0 := by rw [hq, sum_vp]; exact sum_eq_zero r₂
  have hq0 : ¬ (q = 0 ∨ q = onesV) := by
    intro h
    apply S.u1_not_V1
    refine (hβk ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩).1 (Multiplicative.toAdd.injective ?_)
    rw [toAdd_one, ← hr₂]
    refine (mk_eq_zero_iff r₂).2 ?_
    rcases h with h | h
    · left; exact vp_injective τ⁻¹ (by rw [← hq, h, vp_zero])
    · right; exact vp_injective τ⁻¹ (by rw [← hq, h]; exact (vp_const τ⁻¹).symm)
  let f₀ : ↥(evenWeight 6) →+ ZMod 2 :=
    { toFun := fun x => dotv (vp τ⁻¹ (x : Fin 6 → ZMod 2)) q
      map_zero' := by simp only [AddSubgroup.coe_zero]; exact dotv_zero q
      map_add' := fun x y => by
        simp only [AddSubgroup.coe_add]
        rw [vp_add, dotv_add] }
  have hf₀ : ∀ x ∈ constWeight 6, f₀ x = 0 := by
    intro x hx
    rcases (constWeight_iff (x : Fin 6 → ZMod 2)).1 hx with h | h
    · show dotv (vp τ⁻¹ (x : Fin 6 → ZMod 2)) q = 0
      rw [h, vp_zero, dotv_zero]
    · show dotv (vp τ⁻¹ (x : Fin 6 → ZMod 2)) q = 0
      rw [h, vp_const, dotv_ones, hqs]
  let f : AltHeart 6 →+ ZMod 2 := QuotientAddGroup.lift (constWeight 6) f₀ hf₀
  let φ : ↥(conjClosure S.V3 S.G1) →* Multiplicative (ZMod 2) :=
    (AddMonoidHom.toMultiplicative f).comp β
  have hφ : ∀ (u : ↥(conjClosure S.V3 S.G1)) (x : ↥(evenWeight 6)),
      (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
      Multiplicative.toAdd (φ u) = dotv (vp τ⁻¹ (x : Fin 6 → ZMod 2)) q := by
    intro u x hx
    show f (Multiplicative.toAdd (β u)) = _
    rw [← hx]
    rfl
  have hgen : ∀ k ∈ S.K2, ∀ v ∈ S.V3,
      ∃ hx : k * v * k⁻¹ ∈ conjClosure S.V3 S.G1, φ ⟨_, hx⟩ = 1 := by
    intro k hk v hv
    have hkH : k ∈ S.G1 := S.K2_le_G1 hk
    have hx : k * v * k⁻¹ ∈ conjClosure S.V3 S.G1 :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hkH) v).mp
        (S.V3_le_UH hv)
    refine ⟨hx, ?_⟩
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β ⟨v, S.V3_le_UH hv⟩))
    have he := hβe ⟨k, hkH⟩ ⟨v, S.V3_le_UH hv⟩ ⟨_, hx⟩ rfl r hr
    apply Multiplicative.toAdd.injective
    rw [hφ _ _ he, toAdd_one]
    have hku : k * S.u1 * k⁻¹ = S.u1 := by
      have h1 := Subgroup.mem_centralizer_iff.mp (S.K2_le_centralizer hk) S.u1 S.u1_mem_V2
      rw [← h1]; group
    have hkq : vp (ρ' ⟨k, hkH⟩) q = q ∨ vp (ρ' ⟨k, hkH⟩) q = q + onesV := by
      have he2 := hβe ⟨k, hkH⟩ ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩ ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩
        hku.symm r₂ hr₂
      rw [← hr₂, mk_eq_mk_iff] at he2
      have e : vp (ρ' ⟨k, hkH⟩) q = vp τ⁻¹ (vp (ρ ⟨k, hkH⟩) (r₂ : Fin 6 → ZMod 2)) := by
        rw [hq, hρ', ← vp_mul, ← vp_mul]; congr 1; group
      rw [e]
      rcases he2 with h | h
      · left; exact congrArg (vp τ⁻¹) h
      · right; rw [show vp (ρ ⟨k, hkH⟩) (r₂ : Fin 6 → ZMod 2) = _ from h, vp_add, vp_const]
    have hw := S.nat_V3_line hβk hβe hρ' hN' honto' hv r hr
    have e : vp τ⁻¹ ((permWeight 6 (ρ ⟨k, hkH⟩) r : ↥(evenWeight 6)) : Fin 6 → ZMod 2) =
        vp (ρ' ⟨k, hkH⟩) (vp τ⁻¹ (r : Fin 6 → ZMod 2)) := by
      show vp τ⁻¹ (vp (ρ ⟨k, hkH⟩) (r : Fin 6 → ZMod 2)) = _
      rw [hρ', ← vp_mul, ← vp_mul]; congr 1; group
    rw [e]
    have hP := perpAt_all q (ρ' ⟨k, hkH⟩) hql hq0 hkq
    have key : ∀ w, InL e01 e23 w → dotv (vp (ρ' ⟨k, hkH⟩) w) q = 0 := by
      intro w hw
      rcases hw with rfl | rfl | rfl | rfl
      · rw [vp_zero, dotv_zero]
      · exact hP _ (by simp)
      · exact hP _ (by simp)
      · exact hP _ (by simp)
    rcases hw with hw | hw
    · exact key _ hw
    · have h1 := key _ hw
      rw [vp_add, vp_const, dotv_add, dotv_ones, hqs, add_zero] at h1
      exact h1
  have hU21 : S.U21 ≤ φ.ker.map (conjClosure S.V3 S.G1).subtype := by
    refine conjClosure_le fun k hk v hv => ?_
    obtain ⟨hx, h1⟩ := hgen k hk v hv
    exact ⟨⟨_, hx⟩, h1, rfl⟩
  obtain ⟨w, hwl, hws, hwq⟩ := nonPerpAt_all q hqs hq0
  have hsw : ∑ i, vp τ w i = 0 := by rw [sum_vp]; exact hws
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd
    (QuotientAddGroup.mk (⟨vp τ w, mem_ev_of_sum_zero hsw⟩ : ↥(evenWeight 6))))
  have hφu : Multiplicative.toAdd (φ u) = 1 := by
    rw [hφ u ⟨vp τ w, mem_ev_of_sum_zero hsw⟩ (by rw [hu]; rfl)]
    simp only
    rw [vp_inv_vp]
    exact hwq
  have hrange : φ.range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : Multiplicative.toAdd y = 0 ∨ Multiplicative.toAdd y = 1 := by
      generalize Multiplicative.toAdd y = a
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hy with hy | hy
    · have : y = 1 := Multiplicative.toAdd.injective (by rw [hy, toAdd_one])
      rw [this]; exact Subgroup.one_mem _
    · exact ⟨u, Multiplicative.toAdd.injective (by rw [hφu, hy])⟩
  have hcardK : Nat.card φ.ker = 16 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [S.card_UH_nat hβs hβk,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange,
      Subgroup.card_top] at h1
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)]
      simp
    rw [h2] at h1
    omega
  calc Nat.card S.U21 ≤ Nat.card ↥(φ.ker.map (conjClosure S.V3 S.G1).subtype) :=
        Subgroup.card_le_of_le hU21
    _ = Nat.card φ.ker := by
        rw [Nat.card_congr (Subgroup.equivMapOfInjective φ.ker _
          (conjClosure S.V3 S.G1).subtype_injective).toEquiv.symm]
    _ = 16 := hcardK

end NatPerp

end Setting4

end CFSG.Quasithin.H13.A6

