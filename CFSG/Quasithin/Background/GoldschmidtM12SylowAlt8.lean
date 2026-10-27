module

public import CFSG.Quasithin.Background.GoldschmidtM12SylowCore
public import CFSG.Quasithin.Background.GoldschmidtAutM12DataS8

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Assembly.LowTwoRank AutM12Recog

namespace M12Sylow

theorem exists_e16_of_sylow {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hE : IsElemAbelian 2 E) (hc : Nat.card E = 16) (Q : Sylow 2 G) :
    ∃ B : Subgroup ↥(Q : Subgroup G), IsElemAbelian 2 B ∧ Nat.card B = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := IsPGroup.of_card (n := 4) (by rw [hc]; norm_num)
  obtain ⟨Q0, hEQ0⟩ := hp.exists_le_sylow
  have hB0 : IsElemAbelian 2 (E.subgroupOf (Q0 : Subgroup G)) := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨⟨a, ha⟩, ha'⟩ ⟨⟨b, hb⟩, hb'⟩
      apply Subtype.ext
      apply Subtype.ext
      show a * b = b * a
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha'⟩ ⟨b, hb'⟩)
    · rintro ⟨a, ha⟩ ha'
      apply Subtype.ext
      exact hE.2 a ha'
  have hB0c : Nat.card (E.subgroupOf (Q0 : Subgroup G)) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ0).toEquiv, hc]
  let θ : ↥(Q0 : Subgroup G) ≃* ↥(Q : Subgroup G) := Sylow.equiv Q0 Q
  refine ⟨(E.subgroupOf (Q0 : Subgroup G)).map θ.toMonoidHom, isElemAbelian_map _ hB0, ?_⟩
  rw [Subgroup.card_map_of_injective θ.injective, hB0c]

namespace Alt8

@[expose] def gensA : ℕ → ↥(alternatingGroup (Fin 8))
  | 0 => ⟨Tab.S8Cert.gp 0, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
  | 1 => ⟨Tab.S8Cert.gp 1, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
  | 2 => ⟨Tab.S8Cert.gp 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
  | 3 => ⟨Tab.S8Cert.gp 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
  | _ => 1

theorem exists_e16 :
    ∃ E : Subgroup ↥(alternatingGroup (Fin 8)), IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  obtain ⟨hgl, -, -, hE2l, -, -, hE2, -, -, hc2, hs2, -⟩ := Tab.S8Cert.ok
  let R := Tab.permSubRep 8 (alternatingGroup (Fin 8))
  have hlen2 : (Tab.S8Cert.data.gd.take 2 ++ Tab.S8Cert.data.gd.drop 4).length = 4 := by
    simp [hgl]
  have hgd2 : ∀ a, a < 4 →
      R.rel (gensA a) ((Tab.S8Cert.data.gd.take 2 ++ Tab.S8Cert.data.gd.drop 4).getD a R.oneD) := by
    intro a ha
    show RepL _ _
    interval_cases a <;> decide +kernel
  obtain ⟨-, -, hcard⟩ := Tab.card_closure_of_valid (R := R) gensA 4 hlen2 hgd2 hE2
  have hel := Tab.isElemAbelian_of_valid (R := R) gensA 4 hlen2 hgd2 hE2
    (by rw [hE2l]; exact hc2) (by rw [hE2l]; exact hs2)
  exact ⟨_, hel, hcard.trans hE2l⟩

theorem hasE16 (Q : Sylow 2 (alternatingGroup (Fin 8))) :
    ∃ B : Subgroup ↥(Q : Subgroup (alternatingGroup (Fin 8))), IsElemAbelian 2 B ∧
      Nat.card B = 16 := by
  obtain ⟨E, hE, hc⟩ := exists_e16
  exact exists_e16_of_sylow hE hc Q

end Alt8

theorem excl64_alternating_eight : Excl64 (alternatingGroup (Fin 8)) :=
  excl64_of_hasE16 Alt8.hasE16

end M12Sylow

end CFSG.Quasithin.F6
