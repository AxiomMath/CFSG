module

public import CFSG.Quasithin.Vol2.GoldschmidtF431NFTI
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpLocal
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSLocK

public section

namespace CFSG.Quasithin.H13.F431.Lift

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431.F45
  CFSG.Quasithin.H13.F431.NF CFSG.Quasithin.Loc442Q
open scoped commutatorElement

universe u

section Derived

variable {H G : Type*} [Group H] [Group G]

theorem card_commutator_range {S : Subgroup H} {f : S →* G} (hf : Function.Injective f) :
    Nat.card ↥⁅f.range, f.range⁆ = Nat.card ↥⁅S, S⁆ := by
  set W : Subgroup S := ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ with hW
  have h1 : ⁅f.range, f.range⁆ = Subgroup.map f W := by
    rw [hW, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
  have h2 : ⁅S, S⁆ = Subgroup.map S.subtype W := by
    rw [hW, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h1, Subgroup.card_map_of_injective hf]
  conv_rhs => rw [h2, Subgroup.card_map_of_injective S.subtype_injective]

theorem card_commutator_map_conj (g : G) (X : Subgroup G) :
    Nat.card ↥⁅X.map (MulAut.conj g).toMonoidHom, X.map (MulAut.conj g).toMonoidHom⁆ =
      Nat.card ↥⁅X, X⁆ := by
  rw [← Subgroup.map_commutator, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem map_conj_centralizer_singleton (g x : G) :
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨c, hc, rfl⟩
    calc g * c * g⁻¹ * (g * x * g⁻¹) = g * (c * x) * g⁻¹ := by group
      _ = g * (x * c) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * (g * c * g⁻¹) := by group
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
      _ = x * (g⁻¹ * y * g) := by group

end Derived

section Core

variable {Mb : Type u} [Group Mb] [Finite Mb] [DecidableEq Mb] {G : Type} [Group G] [Finite G]
  {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z t : Mb} {b1 : ↥M1 →* G} {b2 : ↥M2 →* G}
  {M1G M2G : Subgroup G} {V L : Subgroup Mb}

theorem local_core3 (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2) (hI : I = {z, t})
    (hrange1 : b1.range = M1G) (hrange2 : b2.range = M2G)
    (hyp1 : ∀ w ∈ centerOf (perfectCore M1G), orderOf w = 2 →
      Subgroup.centralizer ({w} : Set G) ≤ M1G)
    (cz : Subgroup.centralizer ({z} : Set Mb) ≤ M1)
    (ct : Subgroup.centralizer ({t} : Set Mb) ≤ M2) (hzperf : z ∈ centerOf (perfectCore M1))
    (hz3 : ¬ 3 ∣ Nat.card ↥⁅Subgroup.centralizer ({z} : Set Mb),
      Subgroup.centralizer ({z} : Set Mb)⁆)
    (ht3 : 3 ∣ Nat.card ↥⁅Subgroup.centralizer ({t} : Set Mb),
      Subgroup.centralizer ({t} : Set Mb)⁆)
    (LK : LocK T z t V L) :
    ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t) ∧
      Subgroup.centralizer ({amalgamMap b1 b2 z} : Set G) ≤ M1G ∧
      Subgroup.centralizer ({amalgamMap b1 b2 t} : Set G) ≤ M2G := by
  have hz1 : z ∈ M1 := cz (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have ht2 : t ∈ M2 := ct (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hz2 : orderOf z = 2 := D.order_two z D.z_mem
  have hb1 : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set G) ≤ M1G := by
    rw [amalgamMap_of_mem₁ b1 b2 hz1]
    exact hyp1 _ (map_mem_centerOf_perfectCore (b := b1) C.inj₁ hrange1 hz1 hzperf)
      ((orderOf_img C.inj₁ hz1).trans hz2)
  have hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set G) ≤ b1.range := hrange1 ▸ hb1
  have hnf : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t) := by
    intro hc
    obtain ⟨g, hg⟩ := isConj_iff.1 hc
    set Cz := Subgroup.centralizer ({z} : Set Mb) with hCz
    set Ct := Subgroup.centralizer ({t} : Set Mb) with hCt
    set f1 : ↥Cz →* G := b1.comp (Subgroup.inclusion cz) with hf1def
    set f2 : ↥Ct →* G := b2.comp (Subgroup.inclusion ct) with hf2def
    have hf1 : Function.Injective f1 := C.inj₁.comp (Subgroup.inclusion_injective cz)
    have hf2 : Function.Injective f2 := C.inj₂.comp (Subgroup.inclusion_injective ct)
    have hβz : amalgamMap b1 b2 z = b1 ⟨z, hz1⟩ := amalgamMap_of_mem₁ b1 b2 hz1
    have hβt : amalgamMap b1 b2 t = b2 ⟨t, ht2⟩ := amalgamMap_of_mem₂ b1 b2 C.agree ht2
    have hGz : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set G) = f1.range := by
      refine le_antisymm (fun x hx => ?_) ?_
      · obtain ⟨m, rfl⟩ := hb hx
        have hcomm := Subgroup.mem_centralizer_singleton_iff.1 hx
        rw [hβz, ← map_mul, ← map_mul] at hcomm
        have hm : (m : Mb) ∈ Cz := by
          rw [hCz, Subgroup.mem_centralizer_singleton_iff]
          exact congrArg Subtype.val (C.inj₁ hcomm)
        exact ⟨⟨m, hm⟩, rfl⟩
      · rintro _ ⟨c, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff, hβz]
        simp only [hf1def, MonoidHom.comp_apply, ← map_mul]
        exact congrArg b1 (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2))
    have hGt : f2.range ≤ Subgroup.centralizer ({amalgamMap b1 b2 t} : Set G) := by
      rintro _ ⟨c, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hβt]
      simp only [hf2def, MonoidHom.comp_apply, ← map_mul]
      exact congrArg b2 (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2))
    have hcard1 : Nat.card ↥⁅Subgroup.centralizer ({amalgamMap b1 b2 z} : Set G),
        Subgroup.centralizer ({amalgamMap b1 b2 z} : Set G)⁆ = Nat.card ↥⁅Cz, Cz⁆ := by
      rw [hGz]
      exact card_commutator_range hf1
    have hdvd : 3 ∣ Nat.card ↥⁅Subgroup.centralizer ({amalgamMap b1 b2 t} : Set G),
        Subgroup.centralizer ({amalgamMap b1 b2 t} : Set G)⁆ := by
      refine dvd_trans ?_ (Subgroup.card_dvd_of_le (Subgroup.commutator_mono hGt hGt))
      rw [card_commutator_range hf2]
      exact ht3
    have hGt' : Subgroup.centralizer ({amalgamMap b1 b2 t} : Set G) =
        (Subgroup.centralizer ({amalgamMap b1 b2 z} : Set G)).map (MulAut.conj g).toMonoidHom := by
      rw [map_conj_centralizer_singleton, hg]
    rw [hGt', card_commutator_map_conj, hcard1] at hdvd
    exact hz3 hdvd
  exact ⟨hnf, hb1, hrange2 ▸ cent_t_le_oriented D C hI LK cz ct hb hnf⟩

end Core

end CFSG.Quasithin.H13.F431.Lift
