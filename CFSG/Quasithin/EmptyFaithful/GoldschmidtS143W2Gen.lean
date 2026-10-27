module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumA
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Stmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
  CFSG.ComponentClassification.PerfectAutomorphisms

namespace S143

namespace InspW2

@[expose] def NumFactW (F : ∀ (L : Type) [Group L], Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
    ∀ z : L, z * z = 1 → z ∉ Subgroup.center L →
      ∀ (Gc : Type) [Group Gc] [Finite Gc] (ρ : Gc →* MulAut L), Function.Injective ρ →
        (∀ l : L, MulAut.conj l ∈ ρ.range) →
        ∀ ž : Gc, ρ ž = MulAut.conj z →
          ∀ Ŝ : Subgroup Gc, IsPGroup 2 Ŝ → ¬ 2 ∣ Ŝ.index →
            Ŝ ≤ Subgroup.centralizer ({ž} : Set Gc) →
            (Nat.card Ŝ = 2 ^ 5 ∨ Nat.card Ŝ = 2 ^ 6) → (∃ e ∈ Ŝ, orderOf e = 4) →
              Nat.card (Subgroup.centralizer ({ž} : Set Gc)) ≠ 3 * Nat.card Ŝ

theorem exists_orderOf_four {Gc : Type} [Group Gc] {Ŝ E : Subgroup Gc} (hE : E ≤ Ŝ)
    (e : ↥E ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) : ∃ x ∈ Ŝ, orderOf x = 4 := by
  refine ⟨((e.symm (Multiplicative.ofAdd 1, 1) : ↥E) : Gc), hE (e.symm _).2, ?_⟩
  have h1 : orderOf (e.symm (Multiplicative.ofAdd (1 : ZMod 4), 1)) =
      orderOf ((Multiplicative.ofAdd (1 : ZMod 4), 1) :
        Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := MulEquiv.orderOf_eq _ _
  rw [Subgroup.orderOf_coe, h1, Prod.orderOf]
  simp only [orderOf_one, Nat.lcm_one_right]
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

theorem false_of_numFactW {F : ∀ (L : Type) [Group L], Prop} (h : NumFactW F) {L : Type} [Group L]
    [Finite L] (hq : CFSG.IsQuasisimple L) (hF : F L) {Gc : Type} [Group Gc] [Finite Gc]
    {ρ : Gc →* MulAut L} {ž : Gc} {Ŝ Kh : Subgroup Gc} (hin : InspInput ρ ž Ŝ Kh)
    (hz : ∃ z : L, z * z = 1 ∧ ρ ž = MulAut.conj z) : False := by
  obtain ⟨z, hz2, hž⟩ := hz
  have hzc : z ∉ Subgroup.center L := by
    intro hc
    have h1 : ρ ž = 1 := by
      rw [hž]
      ext x
      simp only [MulAut.conj_apply, MulAut.one_apply]
      rw [← Subgroup.mem_center_iff.mp hc x]
      group
    exact hin.ne (hin.inj (by rw [h1, map_one]))
  obtain ⟨E, y, hES, ⟨e⟩, -⟩ := hin.E
  exact h L hq hF z hz2 hzc Gc ρ hin.inj hin.inn ž hž Ŝ hin.sylow.1 hin.sylow.2 hin.cent
    hin.card_S (exists_orderOf_four hES e) hin.card_C

theorem numFactW_of_big_inv {F : ∀ (L : Type) [Group L], Prop}
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      ∀ z : L, z * z = 1 → z ∉ Subgroup.center L → 2 ^ 7 ∣ Nat.card (L ⧸ Subgroup.center L)) :
    NumFactW F := by
  intro L _ _ hq hFL z hz2 hzc Gc _ _ ρ hρ hinn ž _ Ŝ _ hŜodd _ hcard _ _
  exfalso
  have h7 := hF L hq hFL z hz2 hzc
  have hInn : (MulAut.conj : L →* MulAut L).range ≤ ρ.range := by
    rintro _ ⟨l, rfl⟩
    exact hinn l
  have h1 : Nat.card (MulAut.conj : L →* MulAut L).range ∣ Nat.card ρ.range :=
    Subgroup.card_dvd_of_le hInn
  have h2 : Nat.card (MulAut.conj : L →* MulAut L).range = Nat.card (L ⧸ Subgroup.center L) := by
    rw [← Insp7.ker_conj_eq_center]
    exact (Nat.card_congr
      (QuotientGroup.quotientKerEquivRange (MulAut.conj : L →* MulAut L)).toEquiv).symm
  have h3 : Nat.card ρ.range = Nat.card Gc := Nat.card_range_of_injective hρ
  rw [h2, h3] at h1
  have h4 := h7.trans h1
  have h5 := Subgroup.card_mul_index Ŝ
  rcases hcard with hc | hc
  · rw [← h5, hc] at h4
    have : 2 ^ 2 ∣ Ŝ.index := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ 5)).mp
      (by simpa [← pow_add] using h4)
    exact hŜodd (dvd_trans (dvd_pow_self 2 (by norm_num)) this)
  · rw [← h5, hc] at h4
    have : 2 ∣ Ŝ.index := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ 6)).mp
      (by simpa [← pow_add] using h4)
    exact hŜodd this

theorem numFactW_of_big {F : ∀ (L : Type) [Group L], Prop}
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      2 ^ 7 ∣ Nat.card (L ⧸ Subgroup.center L)) : NumFactW F :=
  numFactW_of_big_inv fun L _ _ hq h _ _ _ => hF L hq h

theorem numFactW_of_not_dvd_aut {F : ∀ (L : Type) [Group L], Prop}
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      ¬ 2 ^ 5 ∣ Nat.card (MulAut L)) : NumFactW F := by
  intro L _ _ hq hFL z _ _ Gc _ _ ρ hρ _ ž _ Ŝ _ _ _ hcard _ _
  exfalso
  apply hF L hq hFL
  have h1 : Nat.card Gc ∣ Nat.card (MulAut L) := by
    rw [← Nat.card_range_of_injective hρ]
    exact Subgroup.card_subgroup_dvd_card ρ.range
  have h2 : Nat.card Ŝ ∣ Nat.card Gc := Subgroup.card_subgroup_dvd_card Ŝ
  have h3 : 2 ^ 5 ∣ Nat.card Ŝ := by
    rcases hcard with h | h
    · rw [h]
    · rw [h]
      exact pow_dvd_pow 2 (by norm_num)
  exact h3.trans (h2.trans h1)

theorem cover_data {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L) {Gc : Type}
    [Group Gc] (ρ : Gc →* MulAut L) (hρ : Function.Injective ρ)
    (hinn : ∀ l : L, MulAut.conj l ∈ ρ.range) :
    ∃ ρb : Gc →* MulAut (L ⧸ Subgroup.center L), Function.Injective ρb ∧
      (∀ l : L ⧸ Subgroup.center L, MulAut.conj l ∈ ρb.range) ∧
      (∀ (ž : Gc) (z : L), ρ ž = MulAut.conj z →
        ρb ž = MulAut.conj (QuotientGroup.mk z : L ⧸ Subgroup.center L)) ∧
      CFSG.IsQuasisimple (L ⧸ Subgroup.center L) ∧
      (∀ z : L, z ∉ Subgroup.center L →
        (QuotientGroup.mk z : L ⧸ Subgroup.center L) ∉
          Subgroup.center (L ⧸ Subgroup.center L)) := by
  have hperf : Group.IsPerfect L := hq.1
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2.1
  have hqb : CFSG.IsQuasisimple (L ⧸ Subgroup.center L) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hq.2.2).1
  let ρb : Gc →* MulAut (L ⧸ Subgroup.center L) := (centerQuotientHom L).comp ρ
  have hρb : Function.Injective ρb := (centerQuotientHom_injective L).comp hρ
  have hconj : ∀ l : L, MulAut.conj (QuotientGroup.mk l : L ⧸ Subgroup.center L) =
      centerQuotientHom L (MulAut.conj l) := by
    intro l
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    show (QuotientGroup.mk l : L ⧸ Subgroup.center L) * QuotientGroup.mk x *
        (QuotientGroup.mk l)⁻¹ = (centerQuotientHom L (MulAut.conj l)) (QuotientGroup.mk x)
    have := onCenterQuotient_apply_mk (MulAut.conj l) x
    simp only [QuotientGroup.mk'_apply] at this
    show _ = onCenterQuotient (MulAut.conj l) (QuotientGroup.mk x)
    rw [this]
    simp [MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hcenterb : Subgroup.center (L ⧸ Subgroup.center L) = ⊥ := by
    rcases (Subgroup.center (L ⧸ Subgroup.center L)).normal_of_characteristic.eq_bot_or_eq_top
      with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hqb.2.2
      apply hab
      have : Subsingleton ((L ⧸ Subgroup.center L) ⧸
          Subgroup.center (L ⧸ Subgroup.center L)) := by
        rw [h0]; exact QuotientGroup.subsingleton_quotient_top
      exact Subsingleton.elim _ _
  refine ⟨ρb, hρb, ?_, ?_, hqb, ?_⟩
  · intro l
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective l
    obtain ⟨g, hg⟩ := hinn l
    exact ⟨g, by simp only [ρb, MonoidHom.comp_apply, hg, hconj]⟩
  · intro ž z hž
    simp only [ρb, MonoidHom.comp_apply, hž, hconj]
  · intro z hzc
    rw [hcenterb, Subgroup.mem_bot]
    intro h1
    exact hzc ((QuotientGroup.eq_one_iff z).mp h1)

theorem numFactW_of_union {F G' H : ∀ (L : Type) [Group L], Prop}
    (hFGH : ∀ (L : Type) [Group L], F L → G' L ∨ H L) (hG : NumFactW G') (hH : NumFactW H) :
    NumFactW F := by
  intro L _ _ hq hFL z hz2 hzc Gc _ _ ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard h4
  rcases hFGH L hFL with h | h
  · exact hG L hq h z hz2 hzc Gc ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard h4
  · exact hH L hq h z hz2 hzc Gc ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard h4

end InspW2

end S143

end CFSG.Quasithin
