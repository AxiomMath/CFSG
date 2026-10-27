module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecKIK2a
public import CFSG.Quasithin.Vol2.Ch1ModO2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

structure OddData {Q : Type} [Group Q] (B : Subgroup Q) (s : ℕ) : Prop where
  card : ∃ a, Nat.card ↥B = 2 ^ a * s
  cardQ : Nat.card (ModO2 B) = s
  odd : ∀ N : Subgroup ↥B, N.Normal → Odd (Nat.card N) → N = ⊥

section Quot

variable {A B : Type*} [Group A] [Group B]

theorem nonempty_modO2_equiv (g : A →* B) (hg : Function.Surjective g)
    (hk : IsPGroup 2 ↥g.ker) : Nonempty (A ⧸ CFSG.pCore 2 A ≃* B ⧸ CFSG.pCore 2 B) := by
  set ψ := (QuotientGroup.mk' (CFSG.pCore 2 B)).comp g with hψ
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hg
  have heq : ψ.ker = (CFSG.pCore 2 B).comap g := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hker : ψ.ker = CFSG.pCore 2 A := by
    apply le_antisymm
    · rw [heq]
      exact le_sSup ⟨Subgroup.Normal.comap inferInstance g,
        (CFSG.pCore_isPGroup (p := 2) (G := B)).comap_of_ker_isPGroup g hk⟩
    · rw [heq]
      intro x hx
      have hle : (CFSG.pCore 2 A).map g ≤ CFSG.pCore 2 B :=
        le_sSup ⟨Subgroup.Normal.map inferInstance g hg,
          (CFSG.pCore_isPGroup (p := 2) (G := A)).map g⟩
      exact hle ⟨x, hx, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)⟩

end Quot

theorem oddData_of_equiv {Q : Type} [Group Q] [Finite Q] {B : Subgroup Q} {S : Type*} [Group S]
    (e : ModO2 B ≃* S) (hs : IsSimpleGroup S) (h2 : Even (Nat.card S)) :
    OddData B (Nat.card S) where
  card := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).exists_card_eq
    refine ⟨a, ?_⟩
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B), ha,
      Nat.card_congr e.toEquiv, mul_comm]
  cardQ := Nat.card_congr e.toEquiv
  odd := by
    intro N hN hodd
    have : IsSimpleGroup (ModO2 B) := e.isSimpleGroup
    have hNn := hN.map (QuotientGroup.mk' (CFSG.pCore 2 ↥B)) (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥B)))
      with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hxP : x ∈ CFSG.pCore 2 ↥B := by
        have : QuotientGroup.mk' (CFSG.pCore 2 ↥B) x ∈ N.map (QuotientGroup.mk' _) :=
          ⟨x, hx, rfl⟩
        rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
        exact this
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥B) ⟨x, hxP⟩
      have hk' : (⟨x, hx⟩ : ↥N) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      have hodd' : Odd (orderOf (⟨x, hx⟩ : ↥N)) := hodd.of_dvd_nat (orderOf_dvd_natCard _)
      have := eq_one_of_odd_of_two_pow hodd' hk'
      rw [Subgroup.mem_bot]
      simpa using congrArg Subtype.val this
    · exfalso
      have hdvd : Nat.card (ModO2 B) ∣ Nat.card ↥N := by
        have := Subgroup.card_map_dvd (H := N) (QuotientGroup.mk' (CFSG.pCore 2 ↥B))
        rwa [h, Subgroup.card_top] at this
      rw [Nat.card_congr e.toEquiv] at hdvd
      exact (Nat.not_even_iff_odd.2 (hodd.of_dvd_nat hdvd)) h2

variable {Γ : Type} [Group Γ] {J L : Subgroup Γ}

theorem lbar_modO2_equiv (hLJ : L ≤ J) :
    Nonempty (ModO2 (modO2Image J L) ≃* ↥L ⧸ CFSG.pCore 2 ↥L) := by
  set g : ↥L →* ↥(modO2Image J L) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥J)).subgroupMap (L.subgroupOf J)).comp
      (Subgroup.subgroupOfEquivOfLe hLJ).symm.toMonoidHom with hg
  have hgs : Function.Surjective g :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥J)).subgroupMap_surjective (L.subgroupOf J)).comp
      (Subgroup.subgroupOfEquivOfLe hLJ).symm.surjective
  have hk : IsPGroup 2 ↥g.ker := by
    rintro ⟨x, hx⟩
    rw [MonoidHom.mem_ker] at hx
    have hx' : ((Subgroup.subgroupOfEquivOfLe hLJ).symm x : ↥J) ∈ CFSG.pCore 2 ↥J := by
      have : QuotientGroup.mk' (CFSG.pCore 2 ↥J)
          ((Subgroup.subgroupOfEquivOfLe hLJ).symm x : ↥J) = 1 := congrArg Subtype.val hx
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥J) ⟨_, hx'⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : ↥(CFSG.pCore 2 ↥J) => ((y : ↥J) : Γ)) hk
    simpa using this
  obtain ⟨e⟩ := nonempty_modO2_equiv g hgs hk
  exact ⟨e.symm⟩

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
