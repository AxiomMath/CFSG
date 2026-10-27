module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Cls
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Mod
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Cls

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)

@[expose] def listSub (F : List PL) (h1 : idL ∈ F) (hmul : ∀ a ∈ F, ∀ b ∈ F, comp a b ∈ F) :
    Subgroup Ah where
  carrier := {g | ∃ l ∈ F, RepL l (g : P45)}
  mul_mem' := by
    rintro a b ⟨l, hl, hla⟩ ⟨m, hm, hmb⟩
    exact ⟨comp l m, hmul l hl m hm, repL_mul hla hmb⟩
  one_mem' := ⟨idL, h1, repL_one 45⟩
  inv_mem' := by
    intro a ha
    refine inv_mem_of_mul_closed (S := {g : Ah | ∃ l ∈ F, RepL l (g : P45)})
      ⟨idL, h1, repL_one 45⟩ ?_ ha
    rintro a ⟨l, hl, hla⟩ b ⟨m, hm, hmb⟩
    exact ⟨comp l m, hmul l hl m hm, repL_mul hla hmb⟩

theorem rep_mem_of_card_le (S : Subgroup Ah) {F : List PL} (hnd : F.Nodup)
    (hF : ∀ l ∈ F, ∃ g ∈ S, RepL l (g : P45)) (hcard : Nat.card S ≤ F.length) :
    ∀ g ∈ S, ∃ l ∈ F, RepL l (g : P45) := by
  choose! gf hgf using hF
  have hinj : Function.Injective fun i : Fin F.length =>
      (⟨gf (F.get i), (hgf _ (List.get_mem F i)).1⟩ : ↥S) := by
    intro i j hij
    have h1 : gf (F.get i) = gf (F.get j) := congrArg Subtype.val hij
    have h2 := hgf _ (List.get_mem F i)
    have h3 := hgf _ (List.get_mem F j)
    have : F.get i = F.get j := by
      apply repL_unique h2.2
      rw [h1]
      exact h3.2
    exact (hnd.get_inj_iff).1 this
  have hFin : Nat.card (Fin F.length) = F.length := by simp
  have hbij := hinj.bijective_of_nat_card_le (by omega : Nat.card ↥S ≤ Nat.card (Fin F.length))
  intro g hg
  obtain ⟨i, hi⟩ := hbij.2 ⟨g, hg⟩
  refine ⟨F.get i, List.get_mem F i, ?_⟩
  have h2 := (hgf _ (List.get_mem F i)).2
  have : gf (F.get i) = g := congrArg Subtype.val hi
  rwa [this] at h2

theorem card_listSub {F : List PL} {h1 : idL ∈ F} {hmul : ∀ a ∈ F, ∀ b ∈ F, comp a b ∈ F}
    (hnd : F.Nodup) (hT : ∀ l ∈ F, l ∈ Thl) :
    Nat.card ↥(listSub F h1 hmul) = F.length := by
  apply le_antisymm
  · exact card_le_length_of_reps _ fun g hg => hg
  · exact length_le_card_of_nodup _ hnd fun l hl => by
      obtain ⟨g, -, hrep⟩ := exists_That_of_mem_Thl (hT l hl)
      exact ⟨g, ⟨l, hl, hrep⟩, hrep⟩

theorem twoPart_D
    {P : Subgroup Ah} (hcard : Nat.card ↥(P ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) = 96) :
    twoPart (P ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) = 32 := by
  rw [twoPart_eq_of_card_eq (k := 5) (m := 3) (by norm_num) (by rw [hcard]; norm_num)]
  norm_num

theorem isSylowTwoOf_Tf_D
    {P : Subgroup Ah} (hTP : That ≤ P)
    (hcard : Nat.card ↥(P ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) = 96) :
    IsSylowTwoOf (That ⊓ Subgroup.centralizer ({fhatA} : Set Ah))
      (P ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) :=
  isSylowTwoOf_of_card_eq (inf_le_inf_right _ hTP)
    (isSylowTwoOf_That_Bh.2.1.to_le inf_le_left) (by rw [card_Tf_model, twoPart_D hcard])

theorem rep_mem_D
    {P : Subgroup Ah} (Dw : List (List ℕ)) (Dl : List PL) (hDl : Dl = Dw.map evalAL)
    (hDmem : ∀ w ∈ Dw, aW w ∈ P)
    (hDcomm : ∀ l ∈ Dl, comp l fhatL = comp fhatL l) (hDnd : Dl.Nodup)
    (hDcard : Nat.card ↥(P ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) = 96)
    (hDlen : Dl.length = 96) :
    ∀ g ∈ P ⊓ Subgroup.centralizer ({fhatA} : Set Ah), ∃ l ∈ Dl, RepL l (g : P45) := by
  have hF : ∀ l ∈ Dl, ∃ g ∈ P ⊓ Subgroup.centralizer ({fhatA} : Set Ah), RepL l (g : P45) := by
    intro l hl
    rw [hDl] at hl
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hl
    refine ⟨aW w, ⟨hDmem w hw, Subgroup.mem_centralizer_singleton_iff.2
      (comm_of_comp_comm (v := fhatA) repL_fhat (repL_aW w) ?_)⟩, repL_aW w⟩
    exact hDcomm _ (hDl ▸ List.mem_map.2 ⟨w, hw, rfl⟩)
  exact rep_mem_of_card_le _ hDnd hF (by rw [hDcard, hDlen])

theorem pCoreOf_eq_listSub
    {P : Subgroup Ah} (hTP : That ≤ P) (Dw : List (List ℕ)) (Dl Al : List PL) (gw : List ℕ)
    (hDl : Dl = Dw.map evalAL) (hDmem : ∀ w ∈ Dw, aW w ∈ P)
    (hDcomm : ∀ l ∈ Dl, comp l fhatL = comp fhatL l) (hDnd : Dl.Nodup)
    (hDcard : Nat.card ↥(P ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) = 96)
    (hDlen : Dl.length = 96) (hA1 : idL ∈ Al)
    (hAmul : ∀ a ∈ Al, ∀ b ∈ Al, comp a b ∈ Al)
    (hAD : ∀ a ∈ Al, a ∈ Dl) (hAT : ∀ a ∈ Al, a ∈ Thl)
    (hAnorm : ∀ d ∈ Dl, ∀ a ∈ Al, ∃ a' ∈ Al, comp d a = comp a' d)
    (hgD : gw ∈ Dw)
    (hsyl : ∀ l ∈ Thl, comp l fhatL = comp fhatL l →
      comp (comp (evalAL (invAL gw)) l) (evalAL gw) ∈ Thl → l ∈ Al) :
    pCoreOf 2 (P ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) = listSub Al hA1 hAmul := by
  set D : Subgroup Ah := P ⊓ Subgroup.centralizer ({fhatA} : Set Ah) with hD
  have hcompl := rep_mem_D Dw Dl hDl hDmem hDcomm hDnd hDcard hDlen
  have hwD : ∀ w ∈ Dw, aW w ∈ D := fun w hw =>
    ⟨hDmem w hw, Subgroup.mem_centralizer_singleton_iff.2
      (comm_of_comp_comm (v := fhatA) repL_fhat (repL_aW w)
        (hDcomm _ (hDl ▸ List.mem_map.2 ⟨w, hw, rfl⟩)))⟩
  have hNT : listSub Al hA1 hAmul ≤ That := by
    rintro g ⟨a, ha, hrep⟩
    exact (mem_That_iff g).2 ⟨a, hAT a ha, hrep⟩
  have hND : listSub Al hA1 hAmul ≤ D := by
    rintro g ⟨a, ha, hrep⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (hDl ▸ hAD a ha)
    have : g = aW w := Subtype.ext (eq_of_repL hrep (repL_aW w))
    rw [this]
    exact hwD w hw
  apply le_antisymm
  · intro q hq
    have hSyl := isSylowTwoOf_Tf_D hTP hDcard
    have hq1 : q ∈ That ⊓ Subgroup.centralizer ({fhatA} : Set Ah) :=
      pCoreOf_le_of_isSylowTwoOf hSyl hq
    set g : Ah := aW gw with hg
    have hgD' : g ∈ D := hwD gw hgD
    have hq2 : g⁻¹ * q * g⁻¹⁻¹ ∈ pCoreOf 2 D :=
      (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D
        (D.inv_mem hgD')) q).1 hq
    have hq3 : g⁻¹ * q * g ∈ That ⊓ Subgroup.centralizer ({fhatA} : Set Ah) := by
      have := pCoreOf_le_of_isSylowTwoOf hSyl hq2
      simpa using this
    obtain ⟨lq, hlq, hrepq⟩ := (mem_That_iff q).1 hq1.1
    obtain ⟨l', hl', hrep'⟩ := (mem_That_iff _).1 hq3.1
    have hcomm : comp lq fhatL = comp fhatL lq :=
      comp_comm_of_comm (v := fhatA) repL_fhat hrepq
        (Subgroup.mem_centralizer_singleton_iff.1 hq1.2)
    have h2 : RepL (comp (comp (evalAL (invAL gw)) lq) (evalAL gw)) ((g⁻¹ * q * g : Ah) : P45) :=
      repL_mul (repL_mul (repL_aW_inv gw) hrepq) (repL_aW gw)
    have hmem : comp (comp (evalAL (invAL gw)) lq) (evalAL gw) ∈ Thl := by
      rw [repL_unique h2 hrep']
      exact hl'
    exact ⟨lq, hsyl lq hlq hcomm hmem, hrepq⟩
  · refine CFSG.LieType.BorelTits.le_pCoreOf 2 hND ?_ (isSylowTwoOf_That_Bh.2.1.to_le hNT)
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨a, ha, hrepa⟩ := hn
    obtain ⟨d, hd, hrepd⟩ := hcompl g g.2
    obtain ⟨a', ha', hcom⟩ := hAnorm d hd a ha
    obtain ⟨b, -, hrepb⟩ := exists_That_of_mem_Thl (hAT a' ha')
    have h1 : (g : Ah) * (n : Ah) = b * (g : Ah) := by
      apply Subtype.ext
      apply eq_of_repL (l := comp d a) (repL_mul hrepd hrepa)
      rw [hcom]
      exact repL_mul hrepb hrepd
    have : (g : Ah) * (n : Ah) * (g : Ah)⁻¹ = b := by
      rw [h1]
      group
    show (((g * n * g⁻¹ : ↥D) : Ah)) ∈ listSub Al hA1 hAmul
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, this]
    exact ⟨a', ha', hrepb⟩

theorem centralizer_listSub
    (Dw : List (List ℕ)) (Dl : List PL) (hDl : Dl = Dw.map evalAL)
    (hDmem : ∀ w ∈ Dw, aW w ∈ P1h)
    (hDcomm : ∀ l ∈ Dl, comp l fhatL = comp fhatL l) (hDnd : Dl.Nodup)
    (hDcard : Nat.card ↥(P1h ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) = 96)
    (hDlen : Dl.length = 96) (F : List PL) (h1 : idL ∈ F)
    (hmul : ∀ a ∈ F, ∀ b ∈ F, comp a b ∈ F) (hFT : ∀ a ∈ F, a ∈ Thl) (hx : xL ∈ F)
    (hf : fhatL ∈ F)
    (hcheck : ∀ d ∈ Dl, (∀ a ∈ F, comp d a = comp a d) → d ∈ F) {g : Ah}
    (hg : ∀ a ∈ listSub F h1 hmul, g * a = a * g) : g ∈ listSub F h1 hmul := by
  have hcompl := rep_mem_D Dw Dl hDl hDmem hDcomm hDnd hDcard hDlen
  have hxmem : xA ∈ listSub F h1 hmul := ⟨xL, hx, repL_x⟩
  have hfmem : fhatA ∈ listSub F h1 hmul := ⟨fhatL, hf, repL_fhat⟩
  have hgP : g ∈ P1h := (mul_xA_comm_iff g).1 (hg xA hxmem)
  have hgC : g ∈ Subgroup.centralizer ({fhatA} : Set Ah) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hg fhatA hfmem)
  obtain ⟨d, hd, hrepd⟩ := hcompl g ⟨hgP, hgC⟩
  refine ⟨d, hcheck d hd fun a ha => ?_, hrepd⟩
  obtain ⟨b, -, hrepb⟩ := exists_That_of_mem_Thl (hFT a ha)
  have hbm : b ∈ listSub F h1 hmul := ⟨a, ha, hrepb⟩
  exact comp_comm_of_comm hrepb hrepd (hg b hbm)

end CFSG.Quasithin.H13.F431.U42Aut
