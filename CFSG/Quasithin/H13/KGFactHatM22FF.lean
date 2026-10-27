module

public import CFSG.Quasithin.H13.KGFactFFCenter
public import CFSG.Quasithin.EmptyFaithful.LRed5Plumb

public section

namespace CFSG.Quasithin.H13.KGFFZ

open CFSG.Open (pCoreOf)
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem hasNoFaithfulFF_of_kbar (h56 : AsB56) {H K T : Subgroup G} (hSQ : SQTKGroup ↥H)
    (hK : K ∈ cComp H) (hKn : (K.subgroupOf H).Normal) (hTH : T ≤ H) (hT2 : IsPGroup 2 T)
    (hHeq : H = K ⊔ T) (hq : CFSG.IsQuasisimple (KBar K))
    (hZ : Odd (Nat.card (Subgroup.center (KBar K)))) (hcard : 360 < Nat.card (KBar K))
    (hlist : ∀ (X : Type) [Group X] [Finite X], Nat.card X = Nat.card (KBar K) →
      ¬ B56QuasisimpleList X) :
    HasNoFaithfulFFModulesMod H (pCoreOf 2 H) := by
  intro W _ _ hW ρ hker hff
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  set Γ := ρ.range with hΓ
  set L := (K.subgroupOf H).map ρ with hL
  obtain ⟨e⟩ := LRed5.kbar_equiv_image hK ρ hker
  have hq' : CFSG.IsQuasisimple ↥L := EmptyFaithfulMultiple.FFL.isQuasisimple_of_mulEquiv e hq
  have hLΓ : L ≤ Γ := Subgroup.map_le_range ρ _
  have hn : (L.subgroupOf Γ).Normal := by
    have hrs : L.subgroupOf Γ = (K.subgroupOf H).map ρ.rangeRestrict := by
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, Subtype.ext hxy⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [hrs]
    exact hKn.map ρ.rangeRestrict ρ.rangeRestrict_surjective
  set T₀ := (T.subgroupOf H).map ρ with hT₀
  have hT₀2 : IsPGroup 2 T₀ := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map ρ
  have hT₀Γ : T₀ ≤ Γ := Subgroup.map_le_range ρ _
  have hΓeq : Γ = L ⊔ T₀ := by
    have h1 : (K.subgroupOf H) ⊔ (T.subgroupOf H) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKH hTH, ← hHeq]
      exact Subgroup.subgroupOf_self _
    rw [hΓ, MonoidHom.range_eq_map, ← h1, Subgroup.map_sup]
  have hO2 : pCoreOf 2 Γ = ⊥ := LRed5.pCoreOf_range_eq_bot ρ hker
  have hCL := centralizer_le_of_two_quotient hLΓ hn hT₀Γ hT₀2 hΓeq hO2
  have hC : Odd (Nat.card ↥(Γ ⊓ Subgroup.centralizer (L : Set (MulAut W)))) := by
    set C := Γ ⊓ Subgroup.centralizer (L : Set (MulAut W)) with hCdef
    let f : ↥C →* Subgroup.center ↥L :=
      { toFun := fun c => ⟨⟨c, hCL c.2⟩, Subgroup.mem_center_iff.2 fun l =>
          Subtype.ext (Subgroup.mem_centralizer_iff.1 c.2.2 l l.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun a b h => Subtype.ext (by
      have := congrArg (fun z : Subgroup.center ↥L => ((z : ↥L) : MulAut W)) h
      exact this)
    have hdvd := Subgroup.card_dvd_of_injective f hf
    have hZL : Nat.card (Subgroup.center ↥L) = Nat.card (Subgroup.center (KBar K)) := by
      rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
    rw [hZL] at hdvd
    exact Odd.of_dvd_nat hZ hdvd
  have hcardL : Nat.card ↥L = Nat.card (KBar K) := (Nat.card_congr e.toEquiv).symm
  have hQ : G64.IsQuotientOfSQTKCat ↥Γ :=
    ⟨↥H, inferInstance, inferInstance, ρ.ker, inferInstance, SQTKGroup.isSQTKCat hSQ,
      ⟨(QuotientGroup.quotientKerEquivRange ρ).symm⟩⟩
  have hoff : ∃ A : Subgroup (MulAut W), IsFFStarOffender Γ A := B6.exists_isFFStarOffender hff
  exact false_of_ff_center h56 hW hQ hLΓ hn hq' hC (hcardL ▸ hcard) (hlist _ hcardL) hoff

end CFSG.Quasithin.H13.KGFFZ
