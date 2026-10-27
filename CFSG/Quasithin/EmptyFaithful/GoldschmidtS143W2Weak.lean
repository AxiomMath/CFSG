module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Spor
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Ree

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace S143

namespace InspW2

@[expose] def ResWw (F : ∀ (L : Type) [Group L], Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
    ∀ (Gc : Type) [Group Gc] [Finite Gc] (ρ : Gc →* MulAut L) (ž : Gc) (Ŝ Kh : Subgroup Gc),
      InspInput ρ ž Ŝ Kh →
        (∃ l : L, l * l ∈ Subgroup.center L ∧ ρ ž = MulAut.conj l) → False

theorem resWw_cover {F G' : ∀ (L : Type) [Group L], Prop}
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      G' (L ⧸ Subgroup.center L)) (hG : ResW G') : ResWw F := by
  intro L _ _ hq hFL Gc _ _ ρ ž Ŝ Kh hin hz
  obtain ⟨l, hl2, hž⟩ := hz
  obtain ⟨ρb, hρb, hinnb, hžb, hqb, -⟩ := cover_data hq ρ hin.inj hin.inn
  refine hG (L ⧸ Subgroup.center L) hqb (hF L hq hFL) Gc ρb ž Ŝ Kh
    { hin with inj := hρb, inn := hinnb } ⟨QuotientGroup.mk l, ?_, hžb ž l hž⟩
  rw [← QuotientGroup.mk_mul]
  exact (QuotientGroup.eq_one_iff _).mpr hl2

theorem resWw_sporSmall
    (hsimple : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) →
        IsSimpleGroup (NativeSporadic.Carrier s))
    (hM12 : ResW Insp7.M12Fam) (hrest : NumFactW SporNoM12) : ResWw Insp7.SporSmall :=
  resWw_cover (G' := Insp7.SporSimple) (fun _ _ _ hq h => sporSimple_of_sporSmall hsimple hq h)
    (resW_of_union (G' := Insp7.M12Fam) (H := SporNoM12)
      (fun _ _ ⟨s, hs, he⟩ => by
        rcases hs with rfl | rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inl he)
        · exact Or.inl he
        · exact Or.inr (Or.inr (Or.inl he))
        · exact Or.inr (Or.inr (Or.inr (Or.inl he)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr he))))
      hM12 (resW_of_numFactW hrest))

theorem resWAny_of_big {F : ∀ (L : Type) [Group L], Prop}
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      2 ^ 7 ∣ Nat.card (L ⧸ Subgroup.center L)) : ResWAny F := by
  intro L _ _ hq hFL Gc _ _ ρ ž Ŝ Kh hin
  have h7 := hF L hq hFL
  have hInn : (MulAut.conj : L →* MulAut L).range ≤ ρ.range := by
    rintro _ ⟨l, rfl⟩
    exact hin.inn l
  have h1 : Nat.card (MulAut.conj : L →* MulAut L).range ∣ Nat.card ρ.range :=
    Subgroup.card_dvd_of_le hInn
  have h2 : Nat.card (MulAut.conj : L →* MulAut L).range = Nat.card (L ⧸ Subgroup.center L) := by
    rw [← Insp7.ker_conj_eq_center]
    exact (Nat.card_congr
      (QuotientGroup.quotientKerEquivRange (MulAut.conj : L →* MulAut L)).toEquiv).symm
  have h3 : Nat.card ρ.range = Nat.card Gc := Nat.card_range_of_injective hin.inj
  rw [h2, h3] at h1
  have h4 := h7.trans h1
  have h5 := Subgroup.card_mul_index Ŝ
  rcases hin.card_S with hc | hc
  · rw [← h5, hc] at h4
    have : 2 ^ 2 ∣ Ŝ.index := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ 5)).mp
      (by simpa [← pow_add] using h4)
    exact hin.sylow.2 (dvd_trans (dvd_pow_self 2 (by norm_num)) this)
  · rw [← h5, hc] at h4
    have : 2 ∣ Ŝ.index := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ 6)).mp
      (by simpa [← pow_add] using h4)
    exact hin.sylow.2 this

theorem center_eq_bot_of_simple_quasisimple {L : Type} [Group L] [Finite L]
    (hq : CFSG.IsQuasisimple L) (hs : IsSimpleGroup L) : Subgroup.center L = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ x y : L, x * y = y * x := fun x y =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x
    let _ : CommGroup L := { (inferInstance : Group L) with mul_comm := hcomm }
    have hperf : Group.IsPerfect L := hq.1
    have : Nontrivial L := hs.toNontrivial
    exact Group.IsPerfect.not_isSolvable L inferInstance

@[expose] def InspWiw : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → Insp7.ListCases L →
    ∀ (Gc : Type) [Group Gc] [Finite Gc] (ρ : Gc →* MulAut L) (ž : Gc) (Ŝ Kh : Subgroup Gc),
      InspInput ρ ž Ŝ Kh → (∃ l : L, l * l ∈ Subgroup.center L ∧ ρ ž = MulAut.conj l) →
        StatedClassicalModel L .PSU 3 3 1

theorem inspWi_weak (hW : InspWi)
    (hbig : ∀ s : TauCeti.SporadicName, (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
      2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s))
    (hG24 : ∀ (X : Type) [Group X], ChevalleyExceptionalModel X .G2 2 2 → 2 ^ 9 ∣ Nat.card X)
    (hsimple : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) →
        IsSimpleGroup (NativeSporadic.Carrier s))
    (hL34 : ResW fun L _ => StatedClassicalModel L .PSL 3 2 2)
    (hM12 : ResW Insp7.M12Fam) (hrest : NumFactW SporNoM12) : InspWiw := by
  intro L _ _ hq hlist Gc _ _ ρ ž Ŝ Kh hin hz
  by_cases hZ : Subgroup.center L = ⊥
  · obtain ⟨l, hl2, hl⟩ := hz
    exact hW L hq hlist Gc ρ ž Ŝ Kh hin ⟨l, by simpa [hZ] using hl2, hl⟩
  exfalso
  have hbigL : Insp7.BigDvd L → False := fun h =>
    resWAny_of_big (F := Insp7.BigDvd) (fun _ _ _ _ h => two_pow_seven_of_bigDvd h) L hq h Gc ρ ž
      Ŝ Kh hin
  have bigCase : ∀ s : TauCeti.SporadicName,
      (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
        ((L ⧸ CFSG.pCore 2 L) ≃* NativeSporadic.Carrier s) → False := fun s hs e =>
    hbigL (Insp7.bigDvd_of_cover hq (by rw [Nat.card_congr e.toEquiv]; exact hbig s hs))
  have smallCase : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) →
        ((L ⧸ CFSG.pCore 2 L) ≃* NativeSporadic.Carrier s) → False := fun s hs e =>
    resWw_sporSmall hsimple hM12 hrest L hq ⟨s, hs, ⟨e⟩⟩ Gc ρ ž Ŝ Kh hin hz
  rcases hlist with ⟨hs, -⟩ | ⟨-, hc, hB⟩ | hE | ⟨s, hs, ⟨e⟩⟩
  · exact hZ (center_eq_bot_of_simple_quasisimple hq hs)
  · rcases hB with hL | hG
    · exact resWw_cover (F := fun L _ => Subgroup.center L = CFSG.pCore 2 L ∧
          StatedClassicalModel (L ⧸ CFSG.pCore 2 L) .PSL 3 2 2)
        (G' := fun L _ => StatedClassicalModel L .PSL 3 2 2)
        (fun _ _ _ _ ⟨hc, _, K, hKf, hKfin, hK, ⟨e'⟩⟩ =>
          ⟨‹_›, K, hKf, hKfin, hK, ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans e'⟩⟩) hL34 L hq
        ⟨hc, hL⟩ Gc ρ ž Ŝ Kh hin hz
    · exact hbigL (Insp7.bigDvd_of_cover hq (hG24 _ hG))
  · rcases hE with h | ⟨p, -, h⟩
    · exact hZ (center_eq_bot_of_simple_quasisimple hq
        (CFSG.LieType.Simplicity.fam_PSL_simplicity L 3 3 1 h).2)
    · exact hZ (center_eq_bot_of_simple_quasisimple hq
        (CFSG.LieType.Simplicity.fam_PSL_simplicity L 2 p 1 h).2)
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact smallCase _ (Or.inl rfl) e
    · exact smallCase _ (Or.inr (Or.inl rfl)) e
    · exact smallCase _ (Or.inr (Or.inr (Or.inl rfl))) e
    · exact smallCase _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) e
    · exact bigCase _ (Or.inl rfl) e
    · exact smallCase _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) e
    · exact bigCase _ (Or.inr (Or.inl rfl)) e
    · exact bigCase _ (Or.inr (Or.inr (Or.inl rfl))) e
    · exact bigCase _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) e
    · exact bigCase _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) e

end InspW2

end S143

end CFSG.Quasithin
