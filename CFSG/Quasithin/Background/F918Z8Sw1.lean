module

public import CFSG.Quasithin.Background.F918Z8Sz8
public import CFSG.Quasithin.Background.F918Z7aTypes
public import CFSG.Quasithin.Background.F918Z4bL2
public import CFSG.Quasithin.Background.F918Z4bJ1
public import CFSG.Quasithin.Background.F918Z4bPrime
public import CFSG.Quasithin.Background.F918Z4dAux
public import CFSG.Quasithin.Background.F918J1
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
public import CFSG.Quasithin.Background.F918L1
public import CFSG.Quasithin.Background.F918L2
public import CFSG.Quasithin.Background.F918Z8i

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
open CFSG.Timmesfeld

section Abstract

theorem suzs_a38_two_conj {Q : Type} [Group Q] [Finite Q]
    (h38 : A38ForSQTKCat) (hQ : IsQuotientOfSQTKTC Q) (hO2 : CFSG.pCore 2 Q = ⊥)
    {Kq : Subgroup Q} (hKq : Kq ∈ cComp (⊤ : Subgroup Q)) (hnn : ¬ Kq.Normal) :
    A38Types ↥Kq ∧ ∃ t : Q, ⁅Kq, Kq.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧
      Kq ⊓ Kq.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      ∀ g : Q, Kq.map (MulAut.conj g).toMonoidHom = Kq ∨
        Kq.map (MulAut.conj g).toMonoidHom = Kq.map (MulAut.conj t).toMonoidHom := by
  obtain ⟨Shat, _, φ, hφ, hSQ, Lhat, hLhat, hmap⟩ := exists_sqtk_cover hQ hO2 hKq
  rcases (h38 Shat hSQ Lhat hLhat).1 with hN | ⟨hAT, that, -, hcommh, -, hclos⟩
  · exact absurd (hmap ▸ hN.map φ hφ) hnn
  have hsimple : IsSimpleGroup ↥Lhat :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hAT
  have hnt : Nontrivial ↥Kq := (Subgroup.nontrivial_iff_ne_bot _).2 (ne_bot_of_mem_cComp hKq)
  let ψ : ↥Lhat →* Q := φ.comp Lhat.subtype
  have hrange : ψ.range = Kq := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hmap
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hsimple.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      have h1 : ψ.range = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, rfl⟩
        exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
      rw [hrange] at h1
      exact ne_bot_of_mem_cComp hKq h1
  let e : ↥Lhat ≃* ↥Kq := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hKtype : A38Types ↥Kq := a38Types_congr e hAT
  have hKt : Kq.map (MulAut.conj (φ that)).toMonoidHom =
      (Lhat.map (MulAut.conj that).toMonoidHom).map φ := by
    rw [← hmap]
    exact C2A3Orbits.map_conj_map φ Lhat that
  have hcomm : ⁅Kq, Kq.map (MulAut.conj (φ that)).toMonoidHom⁆ = ⊥ := by
    rw [hKt, ← hmap, ← Subgroup.map_commutator, hcommh, Subgroup.map_bot]
  have hKs : IsSimpleGroup ↥Kq := e.symm.isSimpleGroup
  have hKqZ : Subgroup.center ↥Kq = ⊥ := by
    rcases hKs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Kq) with h | h
    · exact h
    · exfalso
      have hab : ⁅Kq, Kq⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        have := Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top (⟨b, hb⟩ : ↥Kq)) ⟨a, ha⟩
        exact (congrArg Subtype.val this).symm
      exact ne_bot_of_mem_cComp hKq ((perfect_of_mem_cComp hKq).symm.trans hab)
  have hinf : Kq ⊓ Kq.map (MulAut.conj (φ that)).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxZ : (⟨x, hx.1⟩ : ↥Kq) ∈ Subgroup.center ↥Kq := by
      rw [Subgroup.mem_center_iff]
      intro k
      have hk : (k : Q) ∈ Subgroup.centralizer
          ((Kq.map (MulAut.conj (φ that)).toMonoidHom : Subgroup Q) : Set Q) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm k.2
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hk x hx.2).symm
    rw [hKqZ, Subgroup.mem_bot] at hxZ
    exact congrArg Subtype.val hxZ
  refine ⟨hKtype, φ that, hcomm, hinf, ?_⟩
  have hKtc : Kq.map (MulAut.conj (φ that)).toMonoidHom ∈ cComp (⊤ : Subgroup Q) :=
    C2A3Orbits.conj_mem_cComp_top hKq _
  have hKts : IsSimpleGroup ↥(Kq.map (MulAut.conj (φ that)).toMonoidHom) :=
    (A38.conjEquiv (φ that) Kq).symm.isSimpleGroup
  intro g
  by_contra hcon
  push Not at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  have hKgc := C2A3Orbits.conj_mem_cComp_top hKq g
  have hKgs : IsSimpleGroup ↥(Kq.map (MulAut.conj g).toMonoidHom) :=
    (A38.conjEquiv g Kq).symm.isSimpleGroup
  have h1 : ⁅Kq, Kq.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
    (cComp_eq_or_commutator_eq_bot_of_isSimpleGroup hKq hKgc hKs hKgs).resolve_left
      (fun h => hne1 h.symm)
  have h2 : ⁅Kq.map (MulAut.conj (φ that)).toMonoidHom, Kq.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
    (cComp_eq_or_commutator_eq_bot_of_isSimpleGroup hKtc hKgc hKts hKgs).resolve_left
      (fun h => hne2 h.symm)
  have hle : Kq.map (MulAut.conj g).toMonoidHom ≤
      Kq ⊔ Kq.map (MulAut.conj (φ that)).toMonoidHom := by
    rintro y ⟨x, hx, rfl⟩
    rw [← hmap] at hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨gh, rfl⟩ := hφ g
    have hmem : gh * l * gh⁻¹ ∈ conjClosure Lhat ⊤ := mem_conjClosure (Subgroup.mem_top gh) hl
    rw [hclos] at hmem
    have := Subgroup.mem_map_of_mem φ hmem
    rw [Subgroup.map_sup, hmap, ← hKt] at this
    simpa [MulAut.conj_apply] using this
  have hcent : Kq ⊔ Kq.map (MulAut.conj (φ that)).toMonoidHom ≤
      Subgroup.centralizer (Kq.map (MulAut.conj g).toMonoidHom : Set Q) :=
    sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2)
  have hab : ⁅Kq.map (MulAut.conj g).toMonoidHom, Kq.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hle.trans hcent)
  exact ne_bot_of_mem_cComp hKgc ((perfect_of_mem_cComp hKgc).symm.trans hab)

end Abstract

section Translate

variable {Y : Type} [CommGroup Y] [Finite Y]

omit [Finite Y] in
theorem suzs_subgroupOf_inj {Γ H H' : Subgroup (MulAut Y)} (hH : H ≤ Γ) (hH' : H' ≤ Γ)
    (h : H.subgroupOf Γ = H'.subgroupOf Γ) : H = H' := by
  have := congrArg (Subgroup.map Γ.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hH, Subgroup.map_subgroupOf_eq_of_le hH'] at this

omit [Finite Y] in
theorem suzs_subgroupOf_conj {Γ K : Subgroup (MulAut Y)} (hKΓ : K ≤ Γ) (g : ↥Γ) :
    (K.subgroupOf Γ).map (MulAut.conj g).toMonoidHom =
      (conjAutSub (g : MulAut Y) K).subgroupOf Γ := by
  have hle : conjAutSub (g : MulAut Y) K ≤ Γ := by
    rintro _ ⟨y, hy, rfl⟩
    exact Γ.mul_mem (Γ.mul_mem g.2 (hKΓ hy)) (Γ.inv_mem g.2)
  refine Subgroup.map_injective Γ.subtype_injective ?_
  rw [Subgroup.map_subgroupOf_eq_of_le hle]
  have h1 := C2A3Orbits.map_conj_map Γ.subtype (K.subgroupOf Γ) g
  rw [Subgroup.map_subgroupOf_eq_of_le hKΓ] at h1
  rw [← h1]
  rfl

theorem suzs_swap_struct (h38 : A38ForSQTKCat)
    {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}
    {A X K : Subgroup (MulAut Y)} {W : Subgroup Y} (d : SuzData Γ Λ S V A X K W)
    (hmove : ¬ ∀ a ∈ A, conjAutSub a K = K) :
    ∃ a₀ ∈ A, conjAutSub a₀ K ≠ K ∧ A38Types ↥K ∧ ⁅K, conjAutSub a₀ K⁆ = ⊥ ∧
      K ⊓ conjAutSub a₀ K = ⊥ ∧ X = K ⊔ conjAutSub a₀ K ∧
      ∀ a ∈ A, conjAutSub a K = K ∨ conjAutSub a K = conjAutSub a₀ K := by
  have hD := d.loc.std.hyp
  have hKΓ : K ≤ Γ := d.hKc.1
  have hKq' : CFSG.IsQuasisimple ↥K := B1Red.isQuasisimple_of_open d.hKc.2.2
  have hKcΓ : K ∈ cComp Γ := by
    refine CFSG.QuasithinUnique.Id2519.mem_cComp_of_isComponentIn ⟨hKΓ, ?_, ?_⟩
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hKΓ).symm hKq'
    · exact CFSG.QuasithinUnique.Id2519.subgroupOf_isSubnormal_of_open d.hKc.2.1
  have hKq : K.subgroupOf Γ ∈ cComp (⊤ : Subgroup ↥Γ) := subgroupOf_mem_cComp hKcΓ
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hA3⟩, -⟩ := QhatStar_spec d.hA
  have hAΓ : A ≤ Γ := hA2.1
  have hnn : ¬ (K.subgroupOf Γ).Normal := by
    intro hN
    apply hmove
    intro a ha
    have key : ∀ s ∈ Γ, ∀ x ∈ K, s * x * s⁻¹ ∈ K := fun s hs x hx => by
      have := hN.conj_mem ⟨x, hKΓ hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨s, hs⟩
      exact Subgroup.mem_subgroupOf.mp this
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => key a (hAΓ ha) x hx
    · intro h
      have := key a⁻¹ (Γ.inv_mem (hAΓ ha)) _ h
      simpa [mul_assoc] using this
  have hO2 : CFSG.pCore 2 ↥Γ = ⊥ := by
    have h := D31.pCoreOf_eq_bot hD
    unfold pCoreOf at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ Γ.subtype_injective).mp h
  obtain ⟨hKtype, t, hcomm, hinf, hconj⟩ := suzs_a38_two_conj h38 hD.qsqtk hO2 hKq hnn
  have hKtype' : A38Types ↥K := a38Types_congr (Subgroup.subgroupOfEquivOfLe hKΓ) hKtype
  obtain ⟨a₀, ha₀, hne₀⟩ : ∃ a₀ ∈ A, conjAutSub a₀ K ≠ K := by
    by_contra hcon
    push Not at hcon
    exact hmove hcon
  have hconjle : ∀ a ∈ A, conjAutSub a K ≤ Γ := by
    rintro a ha _ ⟨y, hy, rfl⟩
    exact Γ.mul_mem (Γ.mul_mem (hAΓ ha) (hKΓ hy)) (Γ.inv_mem (hAΓ ha))
  have hg0 : (K.subgroupOf Γ).map (MulAut.conj (⟨a₀, hAΓ ha₀⟩ : ↥Γ)).toMonoidHom =
      (conjAutSub a₀ K).subgroupOf Γ := suzs_subgroupOf_conj hKΓ ⟨a₀, hAΓ ha₀⟩
  have hKtE : (conjAutSub a₀ K).subgroupOf Γ =
      (K.subgroupOf Γ).map (MulAut.conj t).toMonoidHom := by
    rcases hconj ⟨a₀, hAΓ ha₀⟩ with h | h
    · exfalso
      rw [hg0] at h
      exact hne₀ (suzs_subgroupOf_inj (hconjle a₀ ha₀) hKΓ h)
    · rw [← hg0]
      exact h
  have hperm : ∀ a ∈ A, conjAutSub a K = K ∨ conjAutSub a K = conjAutSub a₀ K := by
    intro a ha
    have h := hconj ⟨a, hAΓ ha⟩
    rw [suzs_subgroupOf_conj hKΓ] at h
    rcases h with h | h
    · left
      exact suzs_subgroupOf_inj (hconjle a ha) hKΓ h
    · right
      rw [← hKtE] at h
      exact suzs_subgroupOf_inj (hconjle a ha) (hconjle a₀ ha₀) h
  refine ⟨a₀, ha₀, hne₀, hKtype', ?_, ?_, ?_, hperm⟩
  · rw [← hKtE] at hcomm
    have := congrArg (Subgroup.map Γ.subtype) hcomm
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKΓ,
      Subgroup.map_subgroupOf_eq_of_le (hconjle a₀ ha₀), Subgroup.map_bot] at this
  · rw [← hKtE] at hinf
    have := congrArg (Subgroup.map Γ.subtype) hinf
    rwa [Subgroup.map_inf _ _ _ Γ.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hKΓ,
      Subgroup.map_subgroupOf_eq_of_le (hconjle a₀ ha₀), Subgroup.map_bot] at this
  · apply le_antisymm
    · rw [d.hXK]
      refine iSup₂_le fun a ha => ?_
      rcases hperm a ha with h | h
      · rw [h]
        exact le_sup_left
      · rw [h]
        exact le_sup_right
    · refine sup_le ?_ ?_
      · have h1 : conjAutSub (1 : MulAut Y) K = K := Z4d.map_conj_one K
        rw [d.hXK]
        exact le_iSup₂_of_le 1 A.one_mem h1.ge
      · rw [d.hXK]
        exact le_iSup₂_of_le a₀ ha₀ le_rfl
end Translate


section Main

variable {Y : Type} [CommGroup Y] [Finite Y]

theorem suzs_rank_A {K K' A : Subgroup (MulAut Y)}
    {a₀ : MulAut Y} {M : Subgroup Y} {m : ℕ} (hAut : AutRankLe ↥K m)
    (hA : IsElemAbelian2 A) (ha₀ : a₀ ∈ A) (hK' : K' = conjAutSub a₀ K)
    (hperm : ∀ a ∈ A, conjAutSub a K = K ∨ conjAutSub a K = K')
    (hAM : A ≤ stabSub M) (hne : K' ≠ K)
    (hB : ∀ b ∈ A, (∀ x ∈ K ⊔ K', b * x = x * b) → ∀ w ∈ M, b w = w) :
    rk ↥(autSub A M) ≤ m + 1 := by
  set N : Subgroup (MulAut Y) := Subgroup.normalizer (K : Set (MulAut Y)) with hN
  have hmemN : ∀ g : MulAut Y, g ∈ N ↔ conjAutSub g K = K := fun g =>
    Subgroup.mem_normalizer_iff_map_conj_eq
  have ha2 : a₀ * a₀ = 1 := by
    have := hA.2 a₀ ha₀
    rwa [pow_two] at this
  have hc2 : ∀ c ∈ A, c * c = 1 := fun c hc => by
    have := hA.2 c hc
    rwa [pow_two] at this
  have ha₀N : a₀ ∉ N := by
    intro h
    exact hne (hK' ▸ (hmemN a₀).1 h)
  have hc : ∀ c : MulAut Y, c ∈ A → (c ∈ N ↔ ¬ c * a₀ ∈ N) := by
    intro c hc
    constructor
    · intro hcN hctN
      apply ha₀N
      have : a₀ = c⁻¹ * (c * a₀) := by group
      rw [this]
      exact N.mul_mem (N.inv_mem hcN) hctN
    · intro hnot
      by_contra hcN
      apply hnot
      have h1 : conjAutSub c K = K' := (hperm c hc).resolve_left (fun h => hcN ((hmemN c).2 h))
      rw [hmemN]
      have e1 : conjAutSub (c * a₀) K = conjAutSub c (conjAutSub a₀ K) := by
        unfold conjAutSub
        rw [Subgroup.map_map]
        rfl
      have e2 : conjAutSub (a₀ * c) K = conjAutSub a₀ (conjAutSub c K) := by
        unfold conjAutSub
        rw [Subgroup.map_map]
        rfl
      have e3 : conjAutSub a₀ (conjAutSub a₀ K) = K := by
        unfold conjAutSub
        rw [Subgroup.map_map]
        have : (MulAut.conj a₀).toMonoidHom.comp (MulAut.conj a₀).toMonoidHom = MonoidHom.id _ := by
          refine MonoidHom.ext fun g => ?_
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            MonoidHom.id_apply]
          have hainv : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right ha2
          rw [hainv]
          calc a₀ * (a₀ * g * a₀) * a₀ = (a₀ * a₀) * g * (a₀ * a₀) := by group
            _ = g := by rw [ha2]; simp
        rw [this, Subgroup.map_id]
      have hab : c * a₀ = a₀ * c := hA.1 c hc a₀ ha₀
      rw [hab, e2, h1, hK']
      exact e3
  have hidx : N.relIndex A = 2 := by
    show (N.subgroupOf A).index = 2
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a₀, ha₀⟩, fun c => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases h : (c : MulAut Y) ∈ N
    · exact Or.inr ⟨h, (hc c c.2).1 h⟩
    · exact Or.inl ⟨not_not.1 (fun h' => h ((hc c c.2).2 h')), h⟩
  have hcard : Nat.card A = 2 * Nat.card ↥(A ⊓ N) := by
    have := Subgroup.relIndex_mul_card N A
    rw [hidx, inf_comm N A] at this
    exact this.symm
  let ψ : ↥(A ⊓ N) →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right)
  have hel : IsElemAb2 (⊤ : Subgroup ↥(A ⊓ N)) := by
    refine ⟨fun a _ b _ => Subtype.ext (hA.1 a a.2.1 b b.2.1), fun a _ => Subtype.ext ?_⟩
    exact hA.2 a a.2.1
  have hel' : IsElemAb2 ψ.range := by
    have := hel.map ψ
    rwa [← MonoidHom.range_eq_map] at this
  have hrange : rk ψ.range ≤ m := hAut _ hel'
  have hrangecard : Nat.card ψ.range = 2 ^ rk ψ.range := hel'.card_eq_two_pow
  have hA₁card : Nat.card ↥(A ⊓ N) = Nat.card ψ.ker * Nat.card ψ.range := by
    have h1 := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker] at h1
    exact h1.symm
  let Kc : Subgroup (MulAut Y) := ψ.ker.map (A ⊓ N).subtype
  have hKcC : Kc ≤ A ⊓ centSub M := by
    rintro _ ⟨b, hb, rfl⟩
    have hbA : (b : MulAut Y) ∈ A := b.2.1
    refine ⟨hbA, fun w hw => ?_⟩
    have hker : Subgroup.inclusion inf_le_right b ∈ K.normalizerMonoidHom.ker :=
      MonoidHom.mem_ker.mpr hb
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff] at hker
    have hbK : ∀ y ∈ K, (b : MulAut Y) * y = y * b := fun y hy => (hker y hy).symm
    have hab : Commute (b : MulAut Y) a₀ := hA.1 b hbA a₀ ha₀
    have hbK' : ∀ y ∈ K', (b : MulAut Y) * y = y * b := by
      intro y hy
      rw [hK'] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      have h2 : Commute (b : MulAut Y) k := hbK k hk
      exact ((hab.mul_right h2).mul_right hab.inv_right :
        Commute (b : MulAut Y) (a₀ * k * a₀⁻¹))
    have hsup : K ⊔ K' ≤ Subgroup.centralizer {(b : MulAut Y)} := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hbK y hy).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hbK' y hy).symm
    exact hB b hbA (fun y hy => (Subgroup.mem_centralizer_singleton_iff.1 (hsup hy)).symm) w hw
  have hKccard : Nat.card Kc = Nat.card ψ.ker :=
    Subgroup.card_map_of_injective (A ⊓ N).subtype_injective
  obtain ⟨c', hc'⟩ := Subgroup.card_dvd_of_le hKcC
  have hmul := card_autSub_mul hAM
  have hkpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hkey : Nat.card ↥(autSub A M) * c' = 2 * Nat.card ψ.range := by
    have h1 : Nat.card ↥(autSub A M) * (Nat.card ψ.ker * c') =
        2 * (Nat.card ψ.ker * Nat.card ψ.range) := by
      rw [← hKccard, ← hc', hmul, hcard, hA₁card, hKccard]
    have h2 : Nat.card ψ.ker * (Nat.card ↥(autSub A M) * c') =
        Nat.card ψ.ker * (2 * Nat.card ψ.range) := by
      calc Nat.card ψ.ker * (Nat.card ↥(autSub A M) * c')
          = Nat.card ↥(autSub A M) * (Nat.card ψ.ker * c') := by ring
        _ = 2 * (Nat.card ψ.ker * Nat.card ψ.range) := h1
        _ = Nat.card ψ.ker * (2 * Nat.card ψ.range) := by ring
    exact Nat.eq_of_mul_eq_mul_left hkpos h2
  have hdvd : Nat.card ↥(autSub A M) ∣ 2 ^ (1 + rk ψ.range) := by
    refine ⟨c', ?_⟩
    rw [pow_add, ← hrangecard]
    omega
  unfold rk
  calc padicValNat 2 (Nat.card ↥(autSub A M)) ≤ padicValNat 2 (2 ^ (1 + rk ψ.range)) :=
        padicValNat_two_le_of_dvd (by positivity) hdvd
    _ = 1 + rk ψ.range := padicValNat.prime_pow _
    _ ≤ m + 1 := by omega


theorem suzs_card_dvd_sub_one {R : Subgroup Y} {g : MulAut Y} {p : ℕ} [hp : Fact p.Prime]
    (hgR : g ∈ stabSub R) (hgp : g ^ p = 1) (hfree : ∀ v ∈ R, g v = v → v = 1) :
    p ∣ Nat.card ↥R - 1 := by
  classical
  have : Fintype ↥R := Fintype.ofFinite _
  let τ : MulAut ↥R := resHom R ⟨g, hgR⟩
  have hτ : τ ^ p = 1 := by
    have : (⟨g, hgR⟩ : stabSub R) ^ p = 1 := Subtype.ext (by simpa using hgp)
    rw [← map_pow, this, map_one]
  let σ : Equiv.Perm ↥R := MulAut.toPerm _ τ
  have hσ : σ ^ p ^ 1 = 1 := by
    rw [pow_one, ← map_pow, hτ, map_one]
  have h := Equiv.Perm.card_compl_support_modEq hσ
  have hcompl : σ.supportᶜ = {1} := by
    ext v
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
    constructor
    · intro hv
      have : g (v : Y) = v := congrArg Subtype.val hv
      exact Subtype.ext (hfree v v.2 this)
    · rintro rfl
      exact map_one τ
  rw [hcompl, Finset.card_singleton] at h
  rw [Nat.card_eq_fintype_card]
  exact (Nat.modEq_iff_dvd' Fintype.card_pos).1 h


def suzs_norm (u : MulAut Y) (ℓ : ℕ) : Y →* Y where
  toFun v := ∏ j ∈ Finset.range ℓ, (u ^ j) v
  map_one' := by simp
  map_mul' a b := by simp [Finset.prod_mul_distrib]

omit [Finite Y] in
theorem suzs_norm_step {u : MulAut Y} {ℓ : ℕ} (hℓ : 0 < ℓ) (hu : u ^ ℓ = 1) (v : Y) :
    suzs_norm u ℓ (u v) = suzs_norm u ℓ v := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  show ∏ j ∈ Finset.range (k + 1), (u ^ j) (u v) = ∏ j ∈ Finset.range (k + 1), (u ^ j) v
  have h1 : ∀ j : ℕ, (u ^ j) (u v) = (u ^ (j + 1)) v := fun j => by
    rw [pow_succ]; rfl
  simp only [h1]
  rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun j => (u ^ j) v)]
  have : (u ^ (k + 1)) v = (u ^ 0) v := by rw [hu]; simp
  rw [this]

omit [Finite Y] in
theorem suzs_norm_zpow {u : MulAut Y} {ℓ : ℕ} (hℓ : 0 < ℓ) (hu : u ^ ℓ = 1) (i : ℤ) (v : Y) :
    suzs_norm u ℓ ((u ^ i) v) = suzs_norm u ℓ v := by
  induction i using Int.induction_on generalizing v with
  | zero => simp
  | succ i ih =>
    have : (u ^ ((i : ℤ) + 1)) v = u ((u ^ (i : ℤ)) v) := by
      rw [add_comm, zpow_one_add]; rfl
    rw [this, suzs_norm_step hℓ hu, ih]
  | pred i ih =>
    have : (u ^ (-(i : ℤ) - 1)) v = (u ^ (-(i : ℤ) - 1)) v := rfl
    have h2 : (u ^ (-(i : ℤ))) v = u ((u ^ (-(i : ℤ) - 1)) v) := by
      have : (u ^ (-(i : ℤ))) = u * u ^ (-(i : ℤ) - 1) := by
        rw [← zpow_one_add]; congr 1; ring
      rw [this]; rfl
    rw [← suzs_norm_step hℓ hu, ← h2, ih]

omit [Finite Y] in
theorem suzs_norm_commSub {u : MulAut Y} {ℓ : ℕ} (hℓ : 0 < ℓ) (hu : u ^ ℓ = 1) (M : Subgroup Y) :
    ∀ v ∈ commSub M (Subgroup.zpowers u), suzs_norm u ℓ v = 1 := by
  intro v hv
  have : commSub M (Subgroup.zpowers u) ≤ (suzs_norm u ℓ).ker := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, suzs_norm_zpow hℓ hu]
    simp
  exact this hv

omit [Finite Y] in
theorem suzs_fixed_eq_one {u : MulAut Y} {ℓ : ℕ} (hℓ : 0 < ℓ) (hℓ2 : Odd ℓ)
    (hu : u ^ ℓ = 1)
    (hexp : ∀ y : Y, y ^ 2 = 1) (M : Subgroup Y) {v : Y}
    (hv : v ∈ commSub M (Subgroup.zpowers u)) (huv : u v = v) : v = 1 := by
  have hfix : ∀ j : ℕ, (u ^ j) v = v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, MulAut.mul_apply, huv, ih]
  have h1 := suzs_norm_commSub hℓ hu M v hv
  have h2 : suzs_norm u ℓ v = v ^ ℓ := by
    show ∏ j ∈ Finset.range ℓ, (u ^ j) v = v ^ ℓ
    simp [hfix]
  obtain ⟨k, hk⟩ := hℓ2
  rw [h2, hk, pow_succ, pow_mul, hexp, one_pow, one_mul] at h1
  exact h1

theorem suzs_two_rk_le {u a : MulAut Y} {ℓ : ℕ} (hℓ2 : Odd ℓ) (hu : u ^ ℓ = 1)
    (hexp : ∀ y : Y, y ^ 2 = 1) {M : Subgroup Y} (huM : u ∈ stabSub M)
    (hinv : a * u * a⁻¹ = u⁻¹)
    (haR : a ∈ stabSub (commSub M (Subgroup.zpowers u))) :
    2 * rk ↥(commSub M (Subgroup.zpowers u) ⊓ fixV (Subgroup.zpowers a)) ≤
      rk ↥(commSub M (Subgroup.zpowers u)) := by
  set R := commSub M (Subgroup.zpowers u) with hR
  have huR : u ∈ stabSub R :=
    mem_stabSub_commSub huM (Subgroup.le_normalizer (Subgroup.mem_zpowers u))
  obtain ⟨h, hh⟩ := hℓ2
  have hℓpos : 0 < ℓ := by omega
  let δ : ↥R →* ↥R :=
    { toFun := fun r => ⟨a r * (r : Y)⁻¹, R.mul_mem ((haR r).2 r.2) (R.inv_mem r.2)⟩
      map_one' := by ext; simp
      map_mul' := fun r s => by
        ext
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        rw [mul_comm ((s : Y)⁻¹) ((r : Y)⁻¹)]
        exact mul_mul_mul_comm _ _ _ _ }
  let C' : Subgroup ↥R := (R ⊓ fixV (Subgroup.zpowers a)).subgroupOf R
  have hC'ker : C' ≤ δ.ker := by
    intro r hr
    have : a (r : Y) = r := Z4d.mem_fixV_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hr).2
    rw [MonoidHom.mem_ker]
    ext
    show a (r : Y) * (r : Y)⁻¹ = 1
    rw [this, mul_inv_cancel]
  have hC'range : C' ≤ δ.range := by
    intro c hc
    have hcR : (c : Y) ∈ R := c.2
    have hac : a (c : Y) = c := Z4d.mem_fixV_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hc).2
    set f : ℕ → Y := fun j => (u ^ j) (c : Y) with hf
    have hfR : ∀ j, f j ∈ R := fun j => (((stabSub R).pow_mem huR j) (c : Y)).2 hcR
    have hnorm : ∏ j ∈ Finset.range ℓ, f j = 1 := suzs_norm_commSub hℓpos hu M c hcR
    have hconj : ∀ j : ℕ, a * u ^ j = (u⁻¹) ^ j * a := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have h1 : a * u = u⁻¹ * a := by
          have := congrArg (· * a) hinv
          simpa [mul_assoc] using this
        calc a * u ^ (j + 1) = (a * u ^ j) * u := by rw [pow_succ, mul_assoc]
          _ = (u⁻¹) ^ j * (a * u) := by rw [ih, mul_assoc]
          _ = (u⁻¹) ^ j * (u⁻¹ * a) := by rw [h1]
          _ = (u⁻¹) ^ (j + 1) * a := by rw [pow_succ, mul_assoc]
    have ha_f : ∀ j, j ≤ ℓ → a (f j) = f (ℓ - j) := by
      intro j hj
      have h1 : (u⁻¹) ^ j = u ^ (ℓ - j) := by
        have : u ^ (ℓ - j) * u ^ j = 1 := by rw [← pow_add, Nat.sub_add_cancel hj, hu]
        rw [inv_pow]
        exact (eq_inv_of_mul_eq_one_left this).symm
      show a ((u ^ j) (c : Y)) = (u ^ (ℓ - j)) (c : Y)
      have : a ((u ^ j) (c : Y)) = (a * u ^ j) (c : Y) := rfl
      rw [this, hconj j, MulAut.mul_apply, hac, h1]
    set y : Y := ∏ j ∈ Finset.range h, f (j + 1) with hy
    have hyR : y ∈ R := Subgroup.prod_mem _ (fun j _ => hfR (j + 1))
    refine ⟨⟨y, hyR⟩, Subtype.ext ?_⟩
    show a y * y⁻¹ = (c : Y)
    have hay : a y = ∏ j ∈ Finset.range h, f (h + 1 + j) := by
      rw [hy, map_prod]
      have : ∀ j ∈ Finset.range h, a (f (j + 1)) = f (h + 1 + (h - 1 - j)) := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [ha_f (j + 1) (by omega)]
        congr 1
        omega
      rw [Finset.prod_congr rfl this]
      exact Finset.prod_range_reflect (fun j => f (h + 1 + j)) h
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hexp y)
    have hprod : (∏ j ∈ Finset.range (2 * h), f (j + 1)) = (c : Y) := by
      have h1 : ∏ j ∈ Finset.range ℓ, f j = (∏ j ∈ Finset.range (2 * h), f (j + 1)) * f 0 := by
        rw [hh]
        exact Finset.prod_range_succ' f (2 * h)
      rw [h1] at hnorm
      have h0 : f 0 = (c : Y) := by simp [hf]
      rw [h0] at hnorm
      have : (∏ j ∈ Finset.range (2 * h), f (j + 1)) = (c : Y)⁻¹ := eq_inv_of_mul_eq_one_left hnorm
      rw [this]
      exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hexp c)
    rw [hay, hyinv, hy, mul_comm]
    have h2 := Finset.prod_range_add (fun x => f (x + 1)) h h
    rw [two_mul, h2] at hprod
    rw [← hprod]
    congr 1
    refine Finset.prod_congr rfl (fun x _ => ?_)
    congr 1
    omega
  have hcard1 : Nat.card ↥R = Nat.card δ.ker * Nat.card δ.range := by
    have h1 := Subgroup.card_mul_index δ.ker
    rw [Subgroup.index_ker] at h1
    exact h1.symm
  have hC'card : Nat.card C' = Nat.card ↥(R ⊓ fixV (Subgroup.zpowers a)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hk : Nat.card C' ≤ Nat.card δ.ker := Subgroup.card_le_of_le hC'ker
  have hr : Nat.card C' ≤ Nat.card δ.range := Subgroup.card_le_of_le hC'range
  have hRpow : Nat.card ↥R = 2 ^ rk ↥R := card_eq_two_pow hexp R
  have hHpow : Nat.card ↥(R ⊓ fixV (Subgroup.zpowers a)) =
      2 ^ rk ↥(R ⊓ fixV (Subgroup.zpowers a)) := card_eq_two_pow hexp _
  have hsq : Nat.card C' * Nat.card C' ≤ Nat.card ↥R := by
    rw [hcard1]
    exact Nat.mul_le_mul hk hr
  rw [hC'card, hHpow, hRpow, ← pow_add] at hsq
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hsq
  omega

theorem suzs_orderOf_two_dvd_rk {R : Subgroup Y} (hexp : ∀ y : Y, y ^ 2 = 1) {g : MulAut Y}
    {p : ℕ} [hp : Fact p.Prime] (hgR : g ∈ stabSub R) (hgp : g ^ p = 1)
    (hfree : ∀ v ∈ R, g v = v → v = 1) : orderOf (2 : ZMod p) ∣ rk ↥R := by
  have h1 := suzs_card_dvd_sub_one hgR hgp hfree
  rw [card_eq_two_pow hexp R] at h1
  exact orderOf_dvd_of_pow_eq_one ((Bang.dvd_two_pow_sub_one_iff (rk ↥R)).1 h1)

theorem suzs_n_dvd_rk {R : Subgroup Y} (hexp : ∀ y : Y, y ^ 2 = 1) {t : MulAut Y} {n : ℕ}
    (hn : 2 ≤ n) (hn6 : n ≠ 6) (htord : orderOf t = 2 ^ n - 1) (htR : t ∈ stabSub R)
    (hfree : ∀ k : ℕ, ¬ (2 ^ n - 1 ∣ k) → ∀ v ∈ R, (t ^ k) v = v → v = 1) : n ∣ rk ↥R := by
  obtain ⟨q, hq⟩ := exists_isPrimitivePrimeDivisor (k := n) hn hn6
  have : Fact q.Prime := ⟨hq.prime⟩
  obtain ⟨k, hk⟩ := hq.dvd
  have hpos : 0 < 2 ^ n - 1 := by
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hk; omega
    · exact h
  have hgq : (t ^ k) ^ q = 1 := by
    rw [← pow_mul, mul_comm, ← hk, ← htord]
    exact pow_orderOf_eq_one t
  have hgR : t ^ k ∈ stabSub R := (stabSub R).pow_mem htR k
  have hnd : ¬ (2 ^ n - 1 ∣ k) := by
    intro hd
    have h1 : 2 ^ n - 1 ≤ k := Nat.le_of_dvd hk0 hd
    have h2 : 2 ≤ q := hq.prime.two_le
    nlinarith
  have h := suzs_orderOf_two_dvd_rk hexp hgR hgq (hfree k hnd)
  rwa [orderOf_two_eq_of_isPrimitivePrimeDivisor hq (by omega)] at h

omit [Finite Y] in
theorem suzs_mem_normalizer_comm {t u : MulAut Y} (h : t * u = u * t) :
    t ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
  have hc : t ∈ Subgroup.centralizer
      ((Subgroup.zpowers u : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact ((Commute.zpow_left (show Commute u t from h.symm) i)).eq
  exact (Subgroup.centralizer_le_normalizer _) hc

omit [Finite Y] in
theorem suzs_mem_normalizer_inv {a u : MulAut Y} (ha2 : a * a = 1)
    (hinv : a * u * a⁻¹ = u⁻¹) :
    a ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hconj : ∀ i : ℤ, a * u ^ i * a⁻¹ = (u⁻¹) ^ i := by
    intro i
    rw [← hinv]
    exact (conj_zpow).symm
  have hfwd : ∀ h ∈ Subgroup.zpowers u, a * h * a⁻¹ ∈ Subgroup.zpowers u := by
    intro h hh
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [hconj]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers u)) _
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hfwd h, fun hh => ?_⟩
  have := hfwd _ hh
  have e : a * (a * h * a⁻¹) * a⁻¹ = h := by
    rw [hainv]
    calc a * (a * h * a) * a = (a * a) * h * (a * a) := by group
      _ = h := by rw [ha2]; simp
  rwa [e] at this

theorem suzs_rk_autSub_pos {A : Subgroup (MulAut Y)} {M : Subgroup Y} (hA : IsElemAbelian2 A)
    (hAM : A ≤ stabSub M) (h : 0 < rkIdx (fixV (autSub A M))) : 0 < rk ↥(autSub A M) := by
  by_contra h0
  have h0' : rk ↥(autSub A M) = 0 := by omega
  have hdvd : Nat.card ↥(autSub A M) ∣ Nat.card ↥A := Dvd.intro _ (card_autSub_mul hAM)
  have hApow : Nat.card ↥A = 2 ^ rk ↥A := card_eq_two_pow_of_isPGroup hA.isPGroup
  rw [hApow] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hjz : j = 0 := by
    have : rk ↥(autSub A M) = j := by
      unfold rk
      rw [hj, padicValNat.prime_pow]
    omega
  rw [hjz, pow_zero] at hj
  have hbot : autSub A M = ⊥ := Subgroup.card_eq_one.1 hj
  have hfixtop : fixV (autSub A M) = ⊤ := by
    rw [eq_top_iff]
    intro v _ φ hφ
    rw [hbot, Subgroup.mem_bot] at hφ
    rw [hφ]
    rfl
  have hidx0 : rkIdx (fixV (autSub A M)) = 0 := by
    unfold rkIdx
    rw [hfixtop, Subgroup.index_top]
    simp
  omega

theorem suzs_rank_lower (hexp : ∀ y : Y, y ^ 2 = 1)
    {M : Subgroup Y} {t u a₀ : MulAut Y} {A : Subgroup (MulAut Y)} {n ℓ : ℕ}
    (hn3 : 3 ≤ n) (hnodd : Odd n)
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hu : u ^ ℓ = 1) (hunt : ∃ w ∈ M, u w ≠ w)
    (hA : IsElemAbelian2 A) (ha₀ : a₀ ∈ A) (hinv : a₀ * u * a₀⁻¹ = u⁻¹)
    (hAM : A ≤ stabSub M) (huM : u ∈ stabSub M) (htM : t ∈ stabSub M)
    (htord : orderOf t = 2 ^ n - 1)
    (hfree : ∀ k : ℕ, ¬ (2 ^ n - 1 ∣ k) → M ⊓ fixV (Subgroup.zpowers (t ^ k)) = ⊥)
    (htu : t * u = u * t) :
    0 < rk ↥(autSub A M) ∧ Nat.lcm n (orderOf (2 : ZMod ℓ)) ≤ 2 * rkIdx (fixV (autSub A M)) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hℓpos : 0 < ℓ := hℓ.pos
  set R := commSub M (Subgroup.zpowers u) with hR
  have hRM : R ≤ M := commSub_le_of_invariant (fun x hx w hw => by
    have : x ∈ stabSub M := (Subgroup.zpowers_le.2 huM) hx
    exact (this w).2 hw)
  have ha2 : a₀ * a₀ = 1 := by
    have := hA.2 a₀ ha₀
    rwa [pow_two] at this
  have huR : u ∈ stabSub R :=
    mem_stabSub_commSub huM (Subgroup.le_normalizer (Subgroup.mem_zpowers u))
  have htR : t ∈ stabSub R := mem_stabSub_commSub htM (suzs_mem_normalizer_comm htu)
  have haR : a₀ ∈ stabSub R := mem_stabSub_commSub (hAM ha₀) (suzs_mem_normalizer_inv ha2 hinv)
  have hfreeU : ∀ v ∈ R, u v = v → v = 1 := fun v hv huv =>
    suzs_fixed_eq_one hℓpos hℓodd hu hexp M hv huv
  have hfreeT : ∀ k : ℕ, ¬ (2 ^ n - 1 ∣ k) → ∀ v ∈ R, (t ^ k) v = v → v = 1 := by
    intro k hk v hv htv
    have h1 : v ∈ M ⊓ fixV (Subgroup.zpowers (t ^ k)) :=
      ⟨hRM hv, Z4d.mem_fixV_zpowers_iff.2 htv⟩
    rw [hfree k hk] at h1
    exact Subgroup.mem_bot.1 h1
  have hn6 : n ≠ 6 := by
    rintro rfl
    exact absurd hnodd (by decide)
  have hnR : n ∣ rk ↥R := suzs_n_dvd_rk hexp (by omega) hn6 htord htR hfreeT
  have hordR : orderOf (2 : ZMod ℓ) ∣ rk ↥R := suzs_orderOf_two_dvd_rk hexp huR hu hfreeU
  have hR0 : R ≠ ⊥ := by
    obtain ⟨w, hw, hne⟩ := hunt
    intro h0
    have hmem : u w * w⁻¹ ∈ R :=
      Subgroup.subset_closure ⟨u, Subgroup.mem_zpowers u, w, hw, rfl⟩
    rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hne hmem
  have hrkR : 0 < rk ↥R := Nat.pos_of_ne_zero (fun h0 => hR0 ((rk_eq_zero_iff hexp).1 h0))
  have hlcm : Nat.lcm n (orderOf (2 : ZMod ℓ)) ≤ rk ↥R :=
    Nat.le_of_dvd hrkR (Nat.lcm_dvd hnR hordR)
  have hinv2 : 2 * rk ↥(R ⊓ fixV (Subgroup.zpowers a₀)) ≤ rk ↥R :=
    suzs_two_rk_le hℓodd hu hexp huM hinv haR
  have hfixle : fixV A ≤ fixV (Subgroup.zpowers a₀) := fun v hv =>
    Z4d.mem_fixV_zpowers_iff.2 (hv a₀ ha₀)
  have h1 : rk ↥(M ⊓ fixV A) ≤ rk ↥(M ⊓ fixV (Subgroup.zpowers a₀)) :=
    rk_mono (inf_le_inf_left _ hfixle)
  have h2 := rk_sup_add_rk_inf R (M ⊓ fixV (Subgroup.zpowers a₀))
  have h3 : rk ↥(R ⊔ (M ⊓ fixV (Subgroup.zpowers a₀))) ≤ rk ↥M := rk_mono (sup_le hRM inf_le_left)
  have h4 : R ⊓ (M ⊓ fixV (Subgroup.zpowers a₀)) = R ⊓ fixV (Subgroup.zpowers a₀) := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨h, _, h'⟩
      exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨h, hRM h, h'⟩
  rw [h4] at h2
  have h5 := rk_add_rkIdx (fixV (autSub A M))
  have h6 : rk ↥(fixV (autSub A M)) = rk ↥(M ⊓ fixV A) := by
    unfold rk
    rw [← map_subtype_fixV_autSub hAM, Subgroup.card_map_of_injective M.subtype_injective]
  have hfinal : rk ↥R ≤ 2 * rkIdx (fixV (autSub A M)) := by omega
  have hordpos : 0 < orderOf (2 : ZMod ℓ) := by
    rcases Nat.eq_zero_or_pos (orderOf (2 : ZMod ℓ)) with h0 | h0
    · rw [h0] at hordR
      exact absurd (zero_dvd_iff.1 hordR) hrkR.ne'
    · exact h0
  have hlcmpos : 0 < Nat.lcm n (orderOf (2 : ZMod ℓ)) := Nat.lcm_pos (by omega) hordpos
  have hidx : 0 < rkIdx (fixV (autSub A M)) := by omega
  exact ⟨suzs_rk_autSub_pos hA hAM hidx, hlcm.trans hfinal⟩

omit [Finite Y] in
theorem suzs_u_nontrivial {K K' : Subgroup (MulAut Y)} {a₀ : MulAut Y} {M : Subgroup Y}
    {x : MulAut Y} (hKs : IsSimpleGroup ↥K) (hKnab : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a)
    (hK' : K' = conjAutSub a₀ K) (hcomm : ⁅K, K'⁆ = ⊥)
    (hKM : K ≤ stabSub M) (hK'M : K' ≤ stabSub M)
    (hnt : ∃ k ∈ K, ∃ w ∈ M, k w ≠ w) (hx : x ∈ K) (hx1 : x ≠ 1) :
    ∃ w ∈ M, (x * (a₀ * x * a₀⁻¹)⁻¹) w ≠ w := by
  by_contra hcon
  push Not at hcon
  have hx'K' : (a₀ * x * a₀⁻¹) ∈ K' := by
    rw [hK']
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  set x' : MulAut Y := a₀ * x * a₀⁻¹ with hx'def
  have hx'M : ∀ w, x' w ∈ M ↔ w ∈ M := hK'M hx'K'
  have hxx' : ∀ v ∈ M, x v = x' v := by
    intro v hv
    have h1 : x' v ∈ M := (hx'M v).2 hv
    have h2 := hcon (x' v) h1
    have : (x * x'⁻¹) (x' v) = x v := by simp [MulAut.mul_apply]
    rw [this] at h2
    exact h2
  have hcom : ∀ k ∈ K, ∀ w ∈ M, k (x w) = x (k w) := by
    intro k hk w hw
    have hkx' : x' * k = k * x' :=
      Subgroup.mem_centralizer_iff.1
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hk) x' hx'K'
    have hkw : k w ∈ M := ((hKM hk) w).2 hw
    calc k (x w) = k (x' w) := by rw [hxx' w hw]
      _ = (k * x') w := rfl
      _ = (x' * k) w := by rw [hkx']
      _ = x' (k w) := rfl
      _ = x (k w) := (hxx' (k w) hkw).symm
  have hker : ∀ k ∈ K, (∀ w ∈ M, k w = w) → k = 1 := by
    intro k hk hk1
    let N : Subgroup ↥K := (centSub M).subgroupOf K
    have hN : N.Normal := ⟨fun n hn g => by
      refine Subgroup.mem_subgroupOf.2 (fun w hw => ?_)
      have hn' : ∀ u ∈ M, (n : MulAut Y) u = u := Subgroup.mem_subgroupOf.1 hn
      have hg' : (g : MulAut Y)⁻¹ w ∈ M := ((hKM (K.inv_mem g.2)) w).2 hw
      show (g : MulAut Y) ((n : MulAut Y) ((g : MulAut Y)⁻¹ w)) = w
      rw [hn' _ hg']
      simp⟩
    rcases hKs.eq_bot_or_eq_top_of_normal N with h | h
    · have : (⟨k, hk⟩ : ↥K) ∈ N := Subgroup.mem_subgroupOf.2 hk1
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      obtain ⟨k0, hk0, w0, hw0, hne⟩ := hnt
      have : (⟨k0, hk0⟩ : ↥K) ∈ N := h ▸ Subgroup.mem_top _
      exact hne (Subgroup.mem_subgroupOf.1 this w0 hw0)
  have hxc : ∀ k ∈ K, k * x = x * k := by
    intro k hk
    have hcK : k * x * k⁻¹ * x⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk)) (K.inv_mem hx)
    have h1 : k * x * k⁻¹ * x⁻¹ = 1 := by
      refine hker _ hcK (fun w hw => ?_)
      have hw1 : x⁻¹ w ∈ M := ((hKM (K.inv_mem hx)) w).2 hw
      have hw2 : k⁻¹ (x⁻¹ w) ∈ M := ((hKM (K.inv_mem hk)) _).2 hw1
      have := hcom k hk _ hw2
      calc (k * x * k⁻¹ * x⁻¹) w = k (x (k⁻¹ (x⁻¹ w))) := rfl
        _ = x (k (k⁻¹ (x⁻¹ w))) := this
        _ = w := by simp
    have : k * x = x * k := by
      have h2 := mul_inv_eq_one.1 (show (k * x * k⁻¹) * x⁻¹ = 1 from by simpa [mul_assoc] using h1)
      have h3 : k * x * k⁻¹ = x := mul_inv_eq_one.1 (by simpa [mul_assoc] using h1)
      calc k * x = (k * x * k⁻¹) * k := by group
        _ = x * k := by rw [h3]
    exact this
  have hZ : Subgroup.center ↥K = ⊥ := by
    rcases hKs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hKnab
      apply hab
      have := Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top (⟨b, hb⟩ : ↥K)) ⟨a, ha⟩
      exact congrArg Subtype.val this
  have hxZ : (⟨x, hx⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hxc g g.2)
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact hx1 (congrArg Subtype.val hxZ)

theorem suzs_types
    {K : Type} [Group K] [Finite K] (hK : A38Types K) (h3 : 3 ∣ Nat.card K) {n : ℕ}
    (hn3 : 3 ≤ n) (hnodd : Odd n) :
    ∃ (m ℓ : ℕ), AutRankLe K m ∧ ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∣ Nat.card K ∧
      m + 1 < Nat.lcm n (orderOf (2 : ZMod ℓ)) := by
  have h3ord : orderOf (2 : ZMod 3) = 2 := by
    refine orderOf_eq_prime (by decide) (by decide)
  have hlcm3 : Nat.lcm n (orderOf (2 : ZMod 3)) = n * 2 := by
    rw [h3ord]
    exact Nat.Coprime.lcm_eq_mul (Nat.coprime_two_left.mpr hnodd).symm
  rcases Z7a.a38_cases hK with ⟨k, hk, hL⟩ | ⟨k, hk, hL⟩ | hJ | ⟨p, hp, hp7, hL⟩
  · by_cases hsmall : k + 1 < 2 * n
    · exact ⟨k, 3, autRankLe_psl2_two hk hL, Nat.prime_three, by norm_num, h3, by
        rw [hlcm3]; omega⟩
    · obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 2 * k) (by omega) (by omega)
      have hord : orderOf (2 : ZMod r) = 2 * k :=
        orderOf_two_eq_of_isPrimitivePrimeDivisor hr (by omega)
      refine ⟨k, r, autRankLe_psl2_two hk hL, hr.prime, hr.ne_two (by omega), ?_, ?_⟩
      · rw [card_eq_of_isPSL_two_two hL]
        exact hr.dvd.mul_left _
      · rw [hord]
        have hpos : 0 < Nat.lcm n (2 * k) := Nat.lcm_pos (by omega) (by omega)
        have := Nat.le_of_dvd hpos (Nat.dvd_lcm_right n (2 * k))
        omega
  · exact absurd h3 (suz_card_not_three_dvd ⟨k, hL⟩)
  · exact ⟨3, 3, autRankLe_j1 hJ, Nat.prime_three, by norm_num, h3, by rw [hlcm3]; omega⟩
  · exact ⟨2, 3, autRankLe_psl2_prime hp hp7 hL, Nat.prime_three, by norm_num, h3, by
      rw [hlcm3]; omega⟩


theorem suzSingle_proved
    (hB45 : AsB45) (hA21 : AsA21SQTKSection) (hF : Vol2.Ch10.SecA.Facts10_1)
    (hX : Insp5aNonShape) (h38 : A38ForSQTKCat) : SuzSingle := by
  intro Y _ _ Γ Λ S V A X K W d a ha
  by_contra hne
  have hmove : ¬ ∀ a ∈ A, conjAutSub a K = K := fun h => hne (h a ha)
  obtain ⟨a₀, ha₀, hne₀, hK38, hcomm, hinf, hXeq, hperm⟩ := suzs_swap_struct h38 d hmove
  obtain ⟨n, hn⟩ := d.sz
  obtain ⟨P, t, hP, htΛ, htN, htord, hfix⟩ := suz_torus_fix_proved hB45 hA21 hF hX d.loc hn
  obtain ⟨-, a1, ha1, K1, _, _, hn1, hK1, ⟨e⟩⟩ := hn
  have hΛcard : Nat.card ↥Λ =
      (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) := by
    subst hn1
    exact (Nat.card_congr e.toEquiv).trans (CFSG.LieType.Ree.suzuki_order hK1)
  have hn3 : 3 ≤ n := by omega
  have hnodd : Odd n := ⟨a1, by omega⟩
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hA3⟩, -⟩ := QhatStar_spec d.hA
  have hAΓ : A ≤ Γ := hA2.1
  have hAel : IsElemAbelian2 A := hA2.2.2
  have hPΛ : P ≤ Λ := hP.1
  have hcommΛ : ∀ ξ ∈ X ⊔ A, ∀ x ∈ Λ, ξ * x = x * ξ := by
    have hX' : X ≤ Subgroup.centralizer (Λ : Set (MulAut Y)) := fun x hx =>
      Subgroup.mem_centralizer_iff.2 fun y hy => (d.hXc x hx y hy).symm
    have hA' : A ≤ Subgroup.centralizer (Λ : Set (MulAut Y)) := fun a ha =>
      Subgroup.mem_centralizer_iff.2 fun y hy => (d.hAc a ha y hy).symm
    intro ξ hξ x hx
    exact (Subgroup.mem_centralizer_iff.1 (sup_le hX' hA' hξ) x hx).symm
  have hΞW : X ⊔ A ≤ stabSub W := sup_le d.hWX d.hWA
  have hΞM : X ⊔ A ≤ stabSub (W ⊓ fixV P) :=
    quarter_stable (fun ξ hξ x hx => hcommΛ ξ hξ x (hPΛ hx)) hΞW
  have hAM : A ≤ stabSub (W ⊓ fixV P) := le_sup_right.trans hΞM
  have hXM : X ≤ stabSub (W ⊓ fixV P) := le_sup_left.trans hΞM
  have hW4 : Nat.card ↥W = Nat.card ↥(W ⊓ fixV P) ^ 4 := (hfix W d.hWΛ).1
  have hC : Nat.card ↥(W ⊓ fixV A) = Nat.card ↥((W ⊓ fixV P) ⊓ fixV A) ^ 4 := by
    have hU : ∀ l ∈ Λ, ∀ u ∈ W ⊓ fixV A, l u ∈ W ⊓ fixV A := by
      intro l hl u hu
      refine ⟨d.hWΛ l hl u hu.1, fun a ha => ?_⟩
      have := d.hAc a ha l hl
      calc a (l u) = (a * l) u := rfl
        _ = (l * a) u := by rw [this]
        _ = l (a u) := rfl
        _ = l u := by rw [hu.2 a ha]
    have := (hfix _ hU).1
    rwa [inf_right_comm] at this
  have hker : A ⊓ centSub (W ⊓ fixV P) = A ⊓ centSub W := by
    refine le_antisymm (fun a ha => ⟨ha.1, ?_⟩) (fun a ha => ⟨ha.1, fun u hu => ha.2 u hu.1⟩)
    exact trivial_of_trivial_quarter (fun U hU => (hfix U hU).1) d.hWΛ
      (fun l hl => d.hAc a ha.1 l hl) (fun u hu => ha.2 u hu)
  have h4 := rAV_quarter d.hWA hAM hW4 hC hker
  have hrat : rAV (autSub A (W ⊓ fixV P)) ≤ ((1 / 2 : ℚ)) := by
    have := d.hrAU
    linarith

  have hKX : K ≤ X := by rw [hXeq]; exact le_sup_left
  have hK'X : conjAutSub a₀ K ≤ X := by rw [hXeq]; exact le_sup_right
  have hKs : IsSimpleGroup ↥K :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hK38
  have hKnab : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨-, hsimple⟩ := d.hKc.2.2
    have hZ : Subgroup.center ↥K = ⊤ := by
      rw [eq_top_iff]
      intro k _
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcon g g.2 k k.2)
    have : Subsingleton (↥K ⧸ Subgroup.center ↥K) := by
      rw [hZ]
      exact QuotientGroup.subsingleton_quotient_top
    have := hsimple.toNontrivial
    exact not_subsingleton _ ‹_›
  have hKZ : Subgroup.center ↥K = ⊥ := by
    rcases hKs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hKnab
      apply hab
      have := Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top (⟨b, hb⟩ : ↥K)) ⟨a, ha⟩
      exact congrArg Subtype.val this
  have hnosz : ¬ ∃ k, IsSz k ↥K := by
    rintro ⟨k, hk⟩
    apply d.hKns
    refine ⟨k, isSz_congr ?_ hk⟩
    exact ((QuotientGroup.quotientMulEquivOfEq hKZ).trans QuotientGroup.quotientBot).symm
  have h3K : 3 ∣ Nat.card ↥K := a38_three_dvd hK38 hnosz
  obtain ⟨m, ℓ, hAut, hℓ, hℓ2, hℓK, hlt⟩ := suzs_types hK38 h3K hn3 hnodd
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) ℓ hℓK
  set x : MulAut Y := (g : MulAut Y) with hxdef
  have hxK : x ∈ K := g.2
  have hxℓ : x ^ ℓ = 1 := by
    have : g ^ ℓ = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    simpa using congrArg Subtype.val this
  have hx1 : x ≠ 1 := by
    intro hx1
    have : g = 1 := Subtype.ext hx1
    rw [this, orderOf_one] at hg
    exact hℓ.one_lt.ne hg
  have ha2 : a₀ * a₀ = 1 := by
    have := hAel.2 a₀ ha₀
    rwa [pow_two] at this
  have hainv : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right ha2
  set x' : MulAut Y := a₀ * x * a₀⁻¹ with hx'def
  have hx'K' : x' ∈ conjAutSub a₀ K := ⟨x, hxK, by simp [hx'def, MulAut.conj_apply]⟩
  have hxx' : x * x' = x' * x := by
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hxK
    exact (Subgroup.mem_centralizer_iff.1 h1 x' hx'K').symm
  have hx'ℓ : x' ^ ℓ = 1 := by
    rw [hx'def, conj_pow, hxℓ]
    simp
  set u : MulAut Y := x * x'⁻¹ with hudef
  have hcx : Commute x x'⁻¹ := (Commute.inv_right (show Commute x x' from hxx'))
  have hu : u ^ ℓ = 1 := by
    rw [hudef, hcx.mul_pow, hxℓ, inv_pow, hx'ℓ]
    simp
  have hinv : a₀ * u * a₀⁻¹ = u⁻¹ := by
    rw [hudef, hx'def]
    simp [mul_assoc, ha2, hainv]
  have hexp : ∀ y : Y, y ^ 2 = 1 := d.loc.std.hyp.exp
  have hKM : K ≤ stabSub (W ⊓ fixV P) := hKX.trans hXM
  have hK'M : conjAutSub a₀ K ≤ stabSub (W ⊓ fixV P) := hK'X.trans hXM
  have hKnt : ∃ k ∈ K, ∃ w ∈ W ⊓ fixV P, k w ≠ w := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x0, hx0, w, hw, hne⟩ := d.hXnt
    apply hne
    have hKc : K ≤ centSub (W ⊓ fixV P) := fun k hk w hw => hcon k hk w hw
    have hK'c : conjAutSub a₀ K ≤ centSub (W ⊓ fixV P) := by
      rintro _ ⟨k, hk, rfl⟩ w hw
      have h1 : a₀⁻¹ w ∈ W ⊓ fixV P := (((stabSub (W ⊓ fixV P)).inv_mem (hAM ha₀)) w).2 hw
      show (a₀ * k * a₀⁻¹) w = w
      rw [MulAut.mul_apply, MulAut.mul_apply, hcon k hk _ h1]
      simp
    have hXc : X ≤ centSub (W ⊓ fixV P) := by rw [hXeq]; exact sup_le hKc hK'c
    exact trivial_of_trivial_quarter (fun U hU => (hfix U hU).1) d.hWΛ
      (fun l hl => d.hXc x0 hx0 l hl) (fun u hu => hXc hx0 u hu) w hw
  have hunt : ∃ w ∈ W ⊓ fixV P, u w ≠ w :=
    suzs_u_nontrivial hKs hKnab rfl hcomm hKM hK'M hKnt hxK hx1
  have huX : u ∈ X := X.mul_mem (hKX hxK) (X.inv_mem (hK'X hx'K'))
  have huM : u ∈ stabSub (W ⊓ fixV P) := hXM huX
  have htM : t ∈ stabSub (W ⊓ fixV P) := by
    have : Λ ⊓ Subgroup.normalizer (P : Set (MulAut Y)) ≤ stabSub (W ⊓ fixV P) := by
      refine le_stabSub_of_forall_mem fun ξ hξ w hw => ⟨d.hWΛ ξ hξ.1 w hw.1, fun p hp => ?_⟩
      have hmem : ξ⁻¹ * p * ξ ∈ P := by
        have := (Subgroup.mem_normalizer_iff.1
          ((Subgroup.normalizer (P : Set (MulAut Y))).inv_mem hξ.2) p).1 hp
        simpa using this
      calc p (ξ w) = ξ ((ξ⁻¹ * p * ξ) w) := by simp [MulAut.mul_apply]
        _ = ξ w := by rw [hw.2 _ hmem]
    exact this ⟨htΛ, htN⟩
  have hfree : ∀ k : ℕ, ¬ (2 ^ n - 1 ∣ k) → (W ⊓ fixV P) ⊓ fixV (Subgroup.zpowers (t ^ k)) = ⊥ :=
    fun k hk => (hfix W d.hWΛ).2 k hk
  have htu : t * u = u * t := (d.hXc u huX t htΛ).symm
  have hB : ∀ b ∈ A, (∀ y ∈ K ⊔ conjAutSub a₀ K, b * y = y * b) →
      ∀ w ∈ W ⊓ fixV P, b w = w :=
    fun b hb hbX w hw => d.hBW b hb (fun y hy => hbX y (hXeq ▸ hy)) w hw.1
  obtain ⟨hrkpos, hlcm⟩ :=
    suzs_rank_lower hexp hn3 hnodd hℓ hℓ2 hu hunt hAel ha₀ hinv hAM huM htM htord hfree htu
  have hrkA := suzs_rank_A hAut hAel ha₀ rfl hperm hAM hne₀ hB
  have hle : 2 * rkIdx (fixV (autSub A (W ⊓ fixV P))) ≤ rk ↥(autSub A (W ⊓ fixV P)) := by
    unfold rAV at hrat
    have hpos : (0 : ℚ) < (rk ↥(autSub A (W ⊓ fixV P)) : ℚ) := by exact_mod_cast hrkpos
    rw [div_le_iff₀ hpos] at hrat
    have : (2 * rkIdx (fixV (autSub A (W ⊓ fixV P))) : ℚ) ≤
        rk ↥(autSub A (W ⊓ fixV P)) := by linarith
    exact_mod_cast this
  omega


end Main

end CFSG.Quasithin
