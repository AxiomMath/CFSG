module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsIdx
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsSix
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312ExtShapesHat

public section

namespace CFSG.Quasithin.A312Words

open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin
open CFSG.Quasithin.A312ExtShapes
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem closure_comm_of_gens {vl : List Γ} (hc : ∀ a ∈ vl, ∀ b ∈ vl, a * b = b * a) :
    ∀ x ∈ Subgroup.closure {v | v ∈ vl}, ∀ y ∈ Subgroup.closure {v | v ∈ vl}, x * y = y * x := by
  have h1 : Subgroup.closure {v | v ∈ vl} ≤ Subgroup.centralizer {v | v ∈ vl} := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    exact fun b hb => hc b hb a ha
  have h2 : Subgroup.closure {v | v ∈ vl} ≤
      Subgroup.centralizer (Subgroup.closure {v | v ∈ vl} : Set Γ) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    have := Subgroup.mem_centralizer_iff.mp (h1 hb) a ha
    exact this.symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (h2 hx) y hy).symm

theorem closure_sq_of_gens {vl : List Γ} (hc : ∀ a ∈ vl, ∀ b ∈ vl, a * b = b * a)
    (hsq : ∀ a ∈ vl, a * a = 1) : ∀ x ∈ Subgroup.closure {v | v ∈ vl}, x * x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem a ha => exact hsq a ha
  | one => simp
  | mul a b ha hb iha ihb =>
    have hcab : a * b = b * a := closure_comm_of_gens hc a ha b hb
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hcab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha => rw [← mul_inv_rev, iha, inv_one]

variable [Finite Γ] {α : Type} [MulAction Γ α]

theorem isExt_hat_of_data {S B Y : Subgroup Γ} {ol : List Γ} {t : Γ} (hS : IsPGroup 2 S)
    (hB : B ∈ lFamily S) (hY : B ⊔ S = Y) (hid : IdxTwoData Y ol t)
    (hcard : Nat.card Y = 138240) (pt : Fin 6 → α) (hpt : Function.Injective pt)
    (hperm : ∀ g ∈ ol ++ [t], ∀ i, ∃ j, g • pt i = pt j) (y1 y2 : Γ) (hy1 : y1 ∈ Y)
    (hy2 : y2 ∈ Y) (h1 : ∀ i : Fin 6, y1 • pt i = pt (i + 1))
    (h2 : ∀ i : Fin 6, y2 • pt i = pt (Equiv.swap 0 1 i)) (vl : List Γ)
    (hvol : ∀ v ∈ vl, v ∈ Subgroup.closure {g | g ∈ ol})
    (hVnorm : ∀ g ∈ ol ++ [t], ∀ v ∈ Subgroup.closure {v | v ∈ vl},
      g⁻¹ * v * g ∈ Subgroup.closure {v | v ∈ vl})
    (hvc : ∀ a ∈ vl, ∀ b ∈ vl, a * b = b * a) (hvsq : ∀ a ∈ vl, a * a = 1)
    (hvfix : ∀ a ∈ vl, ∀ i, a • pt i = pt i)
    (hVcard : Nat.card (Subgroup.closure {v | v ∈ vl}) = 64) :
    IsExt ↥B (fun V _ => IsE2 6 V) (fun Y _ => IsHat Y (alternatingGroup (Fin 6))) := by
  classical
  obtain ⟨hol, hcommA, hcardle⟩ := perfectCore_quotient hS hB hY hid
  set A : Subgroup Γ := perfectCore Y with hA
  have hAY : A ≤ Y := perfectCore_le Y
  have hperf : ⁅A, A⁆ = A := perfectCore_perfect Y
  have hYst : Y ≤ ptStab (Γ := Γ) pt hpt :=
    hid.gen.trans ((Subgroup.closure_le _).mpr fun g hg => mem_ptStab.mpr (hperm g hg))
  have hYperm : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j := fun z hz => mem_ptStab.mp (hYst hz)
  let ρ := sixHom Y pt hpt hYperm
  have hρs : Function.Surjective ρ := sixHom_surjective Y pt hpt hYperm y1 y2 hy1 hy2 h1 h2
  let ρA : ↥A →* Equiv.Perm (Fin 6) := ρ.comp (Subgroup.inclusion hAY)
  have hAperf : commutator ↥A = ⊤ := Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hperf)
  have hsign : ∀ a : ↥A, Equiv.Perm.sign (ρA a) = 1 := by
    intro a
    have hk : commutator ↥A ≤ (Equiv.Perm.sign.comp ρA).ker :=
      Abelianization.commutator_subset_ker _
    rw [hAperf] at hk
    exact MonoidHom.mem_ker.mp (hk (Subgroup.mem_top a))
  let π : ↥A →* alternatingGroup (Fin 6) :=
    ρA.codRestrict (alternatingGroup (Fin 6))
      fun a => Equiv.Perm.mem_alternatingGroup.mpr (hsign a)
  have hπρ : ∀ a : ↥A, (π a : Equiv.Perm (Fin 6)) = ρ ⟨a.1, hAY a.2⟩ := fun a => rfl
  have hcommY : commutator ↥Y ≤ A.subgroupOf Y := by
    unfold commutator
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    exact Subgroup.commutator_le.mp hcommA g₁.1 g₁.2 g₂.1 g₂.2
  have hπs : Function.Surjective π := by
    intro g
    have hg : (g : Equiv.Perm (Fin 6)) ∈ commutator (Equiv.Perm (Fin 6)) := by
      rw [alternatingGroup.commutator_perm_eq (by simp)]; exact g.2
    have hmap : (commutator ↥Y).map ρ = commutator (Equiv.Perm (Fin 6)) := by
      unfold commutator
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective ρ hρs]
    rw [← hmap] at hg
    obtain ⟨y, hy, hyg⟩ := hg
    have hyA : y.1 ∈ A := hcommY hy
    exact ⟨⟨y.1, hyA⟩, Subtype.ext (by rw [hπρ]; exact hyg)⟩
  have hy2A : y2 ∉ A := by
    intro h
    have hsg := hsign ⟨y2, h⟩
    have e2 : ρA ⟨y2, h⟩ = Equiv.swap 0 1 :=
      Equiv.ext fun i => sixHom_eq_of Y pt hpt hYperm ⟨y2, hy2⟩ i _ (h2 i)
    rw [e2, Equiv.Perm.sign_swap (by decide)] at hsg
    exact absurd hsg (by decide)
  have hindex : 2 * Nat.card A ≤ Nat.card Y := by
    have h5 := Subgroup.card_mul_index (A.subgroupOf Y)
    have h6 : Nat.card (A.subgroupOf Y) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv
    have hne : (A.subgroupOf Y).index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one]
      intro htop
      have : (⟨y2, hy2⟩ : ↥Y) ∈ A.subgroupOf Y := by rw [htop]; exact Subgroup.mem_top _
      exact hy2A this
    have hpos : 0 < (A.subgroupOf Y).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h2le : 2 ≤ (A.subgroupOf Y).index := by omega
    rw [h6] at h5
    calc 2 * Nat.card A ≤ (A.subgroupOf Y).index * Nat.card A := Nat.mul_le_mul_right _ h2le
      _ = Nat.card Y := by rw [mul_comm]; exact h5
  have hcardA : Nat.card A = 69120 := by omega
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide
  have hcardA' : Nat.card A = Nat.card (alternatingGroup (Fin 6)) * Nat.card π.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    rwa [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv] at h1
  rw [hA6] at hcardA'
  have hkerc : Nat.card π.ker = 192 := by omega
  set V : Subgroup Γ := Subgroup.closure {v | v ∈ vl} with hVdef
  have hVA : V ≤ A := by
    refine (Subgroup.closure_le A).mpr fun v hv => ?_
    exact (Subgroup.closure_le A).mpr (fun g hg => hol g hg) (hvol v hv)
  have hinvmem : ∀ g ∈ ol ++ [t], g⁻¹ ∈ ol ++ [t] := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact List.mem_append_left _ (hid.inv g hg)
    · have : g = t := by simpa using hg
      subst this
      have hti : g⁻¹ = g := inv_eq_of_mul_eq_one_right hid.tsq
      rw [hti]
      exact List.mem_append_right _ (List.mem_singleton_self g)
  have hnormG : ∀ g ∈ ol ++ [t], g ∈ Subgroup.normalizer (V : Set Γ) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := hVnorm g⁻¹ (hinvmem g hg) h hh
      simpa using this
    · intro hh
      have := hVnorm g hg _ hh
      simpa [mul_assoc] using this
  have hYnorm : Y ≤ Subgroup.normalizer (V : Set Γ) :=
    hid.gen.trans ((Subgroup.closure_le _).mpr hnormG)
  have hVn : (V.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVA).mpr (hAY.trans hYnorm)
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := closure_comm_of_gens hvc
  have hVsq : ∀ x ∈ V, x * x = 1 := closure_sq_of_gens hvc hvsq
  have hVfix : V ≤ ⨅ i, MulAction.stabilizer Γ (pt i) := by
    rw [hVdef, Subgroup.closure_le]
    intro v hv
    simp only [SetLike.mem_coe, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
    exact fun i => hvfix v hv i
  have hVπ : V.subgroupOf A ≤ π.ker := by
    intro x hx
    have hxV : x.1 ∈ V := hx
    have hfix : ∀ i, (x.1 : Γ) • pt i = pt i := fun i => by
      have := Subgroup.mem_iInf.mp (hVfix hxV) i
      exact MulAction.mem_stabilizer_iff.mp this
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hπρ]
    exact Equiv.ext fun i => by
      simpa using sixHom_eq_of Y pt hpt hYperm ⟨x.1, hAY x.2⟩ i i (hfix i)
  have hVcard' : Nat.card (V.subgroupOf A) = 2 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv, hVcard]
    norm_num
  refine isExt_e2_hat6_of_lFamily hB hY hAY hcommA hperf (V.subgroupOf A)
    (fun x hx y hy => Subtype.ext (hVc x.1 hx y.1 hy)) (fun x hx => Subtype.ext (hVsq x.1 hx))
    hVcard' π hπs hVπ ?_
  rw [hkerc, hVcard']
  norm_num

end CFSG.Quasithin.A312Words
