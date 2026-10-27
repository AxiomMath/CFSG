module

public import CFSG.Quasithin.Vol2.KGFactJ4GenL52
public import CFSG.Quasithin.Vol2.KGFactJ4BlockA
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Cases
public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4GB

public section

namespace CFSG.Quasithin.H13.Ch4.J4Blk

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem finite_J : Finite J :=
  Nat.finite_of_card_ne_zero (by rw [card_J j4Facts]; norm_num)

attribute [local instance] finite_J

theorem not_le_of_dvd_twentythree
    {Y : Subgroup J} (h23 : 23 ∣ Nat.card Y) :
    ¬ Y ≤ Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J) ∧
      ¬ Y ≤ Subgroup.normalizer (CFSG.Quasithin.J4Loc.V0 : Set J) := by
  have hF : J4Facts := j4Facts
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have hM2 := G443J4.JM.not_dvd_card_M2 hF
  refine ⟨fun h => hM2 (h23.trans (Subgroup.card_dvd_of_le h)), fun h => ?_⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 23 h23
  have hord : orderOf (y : J) = 23 := by rw [Subgroup.orderOf_coe]; exact hy
  have hVC := G443J4.le_centralizer_of_card_lt hord (h y.2)
    (by rw [CFSG.Quasithin.J4L4.card_V0 hF.mat]; norm_num)
  have hz0 : CFSG.Quasithin.J4Loc.z0 ∈ CFSG.Quasithin.J4Loc.V0 :=
    Subgroup.subset_closure (by simp [CFSG.Quasithin.J4Loc.z0])
  have hyC : (y : J) ∈ Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J) := by
    have := hVC hz0
    rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
    exact this.symm
  exact hM2 (hord ▸ Subgroup.orderOf_dvd_natCard _ hyC)

theorem le_Hj_of_two_local
    {Y : Subgroup J}
    (hY : P0 ≤ Y) {N : Subgroup J} (hN : IsPGroup 2 ↥N) (hne : N ≠ ⊥)
    (hNY : ∀ y ∈ Y, ∀ x ∈ N, y * x * y⁻¹ ∈ N) (h23 : 23 ∣ Nat.card Y) : Y ≤ Hj := by
  obtain ⟨h1, h2⟩ := not_le_of_dvd_twentythree h23
  rcases CFSG.Quasithin.J4Loc.overgroup_of_normal_two_subgroup
      CFSG.Quasithin.J4Loc.j4TwoLocalOvergroups hY hN hne hNY with h | h | h
  · exact h
  · exact absurd h h1
  · exact absurd h h2

theorem twentythree_dvd_card_Hj : 23 ∣ Nat.card Hj := by
  rw [card_Hj j4Facts]; norm_num

theorem exists_conj_eq_Hj
    {B N : Subgroup J}
    (hcard : Nat.card B = 501397585920) (hN : IsPGroup 2 ↥N) (hne : N ≠ ⊥)
    (hNB : B ≤ Subgroup.normalizer (N : Set J)) :
    ∃ g : J, B.map (MulAut.conj g).toMonoidHom = Hj := by
  have hF : J4Facts := j4Facts
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥B) 2
    (show 2 ^ 21 ∣ Nat.card ↥B by rw [hcard]; norm_num)
  set S : Subgroup J := S'.map B.subtype with hS
  have hSc : Nat.card S = 2 ^ 21 := by
    rw [hS, Subgroup.card_map_of_injective B.subtype_injective, hS']
  have hSB : S ≤ B := Subgroup.map_subtype_le S'
  obtain ⟨g, hg⟩ := exists_conj_le_P0 hF.mat hF S (IsPGroup.of_card hSc)
  set Y : Subgroup J := B.map (MulAut.conj g⁻¹).toMonoidHom with hY
  have hSP : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ P0 := by
    rintro _ ⟨s, hs, rfl⟩
    simpa using hg s hs
  have hSP' : S.map (MulAut.conj g⁻¹).toMonoidHom = P0 :=
    Subgroup.eq_of_le_of_card_ge hSP (by
      rw [card_P0 hF.mat hF, G443J4.L52.card_map_conj, hSc])
  have hPY : P0 ≤ Y := hSP' ▸ Subgroup.map_mono hSB
  have hNY : ∀ y ∈ Y, ∀ x ∈ N.map (MulAut.conj g⁻¹).toMonoidHom,
      y * x * y⁻¹ ∈ N.map (MulAut.conj g⁻¹).toMonoidHom := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨n, hn, rfl⟩
    refine ⟨b * n * b⁻¹, (Subgroup.mem_normalizer_iff.mp (hNB hb) n).mp hn, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hYH : Y ≤ Hj := le_Hj_of_two_local hPY (hN.map _)
    (fun h => hne (by
      rw [eq_bot_iff]
      intro n hn
      have : (MulAut.conj g⁻¹).toMonoidHom n ∈ N.map (MulAut.conj g⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hn
      rw [h, Subgroup.mem_bot] at this
      exact (map_eq_one_iff _ (MulAut.conj g⁻¹).injective).mp this))
    hNY (by rw [hY, G443J4.L52.card_map_conj, hcard]; norm_num)
  exact ⟨g⁻¹, Subgroup.eq_of_le_of_card_ge hYH (by
    rw [G443J4.L52.card_map_conj, hcard, card_Hj hF])⟩

theorem Hj_le_normalizer_Eg :
    Hj ≤ Subgroup.normalizer (Eg uJ 11 : Set J) := fun h hh =>
  Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx =>
    eg_normalizes (elem_uJ j4Facts.mat) Hj XJ act letters
      (fun _ hℓ c => hX_all j4Facts.mat hℓ c) (fun _ hℓ => XJ_inv hℓ) Hj_le_closure h hh x hx,
    fun hx => by
      have := eg_normalizes (elem_uJ j4Facts.mat) Hj XJ act letters
        (fun _ hℓ c => hX_all j4Facts.mat hℓ c) (fun _ hℓ => XJ_inv hℓ) Hj_le_closure h⁻¹
        (Hj.inv_mem hh) _ hx
      simpa [mul_assoc] using this⟩

theorem Eg_ne_bot :
    Eg uJ 11 ≠ ⊥ := fun h => by
  have := card_Eg_uJ j4Facts.mat
  rw [h, Subgroup.card_bot] at this
  norm_num at this

theorem normalizer_Eg :
    Subgroup.normalizer (Eg uJ 11 : Set J) = Hj := by
  refine le_antisymm (le_Hj_of_two_local (P0_le_Hj.trans Hj_le_normalizer_Eg)
    (isPGroup_Eg (elem_uJ j4Facts.mat)) Eg_ne_bot (fun y hy x hx =>
      (Subgroup.mem_normalizer_iff.mp hy x).mp hx) ?_) Hj_le_normalizer_Eg
  exact twentythree_dvd_card_Hj.trans (Subgroup.card_dvd_of_le Hj_le_normalizer_Eg)

theorem centralizer_Eg :
    Subgroup.centralizer (Eg uJ 11 : Set J) = Eg uJ 11 := by
  apply le_antisymm
  · intro x hx
    have hxH : x ∈ Hj := normalizer_Eg ▸ Subgroup.centralizer_le_normalizer _ hx
    exact centralizer_Hj j4Facts.mat j4Facts x hxH fun y hy =>
      (Subgroup.mem_centralizer_iff.mp hx y hy).symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Eg_comm (elem_uJ j4Facts.mat) hy hx

theorem minimal_Eg
    (D : Subgroup J) (hDE : D ≤ Eg uJ 11) (hD : Hj ≤ Subgroup.normalizer (D : Set J)) :
    D = ⊥ ∨ D = Eg uJ 11 :=
  minimal_of_orbits (elem_uJ j4Facts.mat) Hj XJ act letters (fun _ hℓ => XJ_mem hℓ)
    (fun _ hℓ c => hX_all j4Facts.mat hℓ c) orbits orbit_words orbit_cover orbit_span D hDE
    fun _ hg d hd => (Subgroup.mem_normalizer_iff.mp (hD hg) d).mp hd

theorem normalizer_Hj :
    Subgroup.normalizer (Hj : Set J) = Hj := by
  refine le_antisymm (le_Hj_of_two_local (P0_le_Hj.trans Subgroup.le_normalizer)
    (pCoreOf_isPGroup 2 Hj) ?_ (fun y hy x hx =>
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 Hj hy) x).mp hx) ?_)
    Subgroup.le_normalizer
  · intro h
    apply Eg_ne_bot
    rw [eq_bot_iff, ← h]
    exact le_pCoreOf_of_le_normalizer 2 Eg_le_Hj Hj_le_normalizer_Eg
      (isPGroup_Eg (elem_uJ j4Facts.mat))
  · exact twentythree_dvd_card_Hj.trans (Subgroup.card_dvd_of_le Subgroup.le_normalizer)

theorem pCoreOf_Hj :
    pCoreOf 2 Hj = Eg uJ 11 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 Hj with hQ
  have hEQ : Eg uJ 11 ≤ Q := le_pCoreOf_of_le_normalizer 2 Eg_le_Hj Hj_le_normalizer_Eg
    (isPGroup_Eg (elem_uJ j4Facts.mat))
  have hQH : Q ≤ Hj := pCoreOf_le 2 Hj
  have hne := inf_centralizer_ne_bot (pCoreOf_isPGroup 2 Hj) (hQH.trans Hj_le_normalizer_Eg)
    (show 2 ∣ Nat.card ↥(Eg uJ 11) by rw [card_Eg_uJ j4Facts.mat]; norm_num)
  have hN : Hj ≤ Subgroup.normalizer
      ((Eg uJ 11 ⊓ Subgroup.centralizer (Q : Set J) : Subgroup J) : Set J) := by
    intro h hh
    refine Subgroup.mem_normalizer_fintype fun c hc => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (Hj_le_normalizer_Eg hh) c).mp hc.1
    · show h * c * h⁻¹ ∈ Subgroup.centralizer (Q : Set J)
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hq' : h⁻¹ * q * h ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_pCoreOf 2 Hj (Hj.inv_mem hh)) q).mp hq
        simpa using this
      have hc' := Subgroup.mem_centralizer_iff.mp hc.2 _ hq'
      calc q * (h * c * h⁻¹) = h * ((h⁻¹ * q * h) * c) * h⁻¹ := by group
        _ = h * (c * (h⁻¹ * q * h)) * h⁻¹ := by rw [hc']
        _ = h * c * h⁻¹ * q := by group
  rcases minimal_Eg _ inf_le_left hN with h | h
  · exact absurd h hne
  · have hEC : Eg uJ 11 ≤ Subgroup.centralizer (Q : Set J) := h.symm.le.trans inf_le_right
    refine le_antisymm ?_ hEQ
    calc Q ≤ Subgroup.centralizer (Eg uJ 11 : Set J) := Subgroup.le_centralizer_iff.mp hEC
      _ = Eg uJ 11 := centralizer_Eg

theorem exists_orderOf_three_Hj :
    ∃ x ∈ Hj, orderOf x = 3 ∧ 4 ≤ Nat.card ↥(Eg uJ 11 ⊓ Subgroup.centralizer ({x} : Set J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P', hP'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Hj) 3
    (show 3 ^ 3 ∣ Nat.card ↥Hj by rw [card_Hj j4Facts]; norm_num)
  have hPc : Nat.card ↥(P'.map Hj.subtype) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective Hj.subtype_injective, hP']
  have hPH : P'.map Hj.subtype ≤ Hj := Subgroup.map_subtype_le P'
  obtain ⟨x, hxP, hx3, h4⟩ := exists_orderOf_three_four_le_card (IsPGroup.of_card hPc)
    (hPH.trans Hj_le_normalizer_Eg) (c := 2) (by norm_num [card_Eg_uJ j4Facts.mat])
    (by norm_num) (by rw [hPc, card_Eg_uJ j4Facts.mat]; norm_num)
  exact ⟨x, hPH hxP, hx3, h4⟩

theorem M4_le_normalizer_F4 :
    CFSG.Quasithin.KGJ4.M4 ≤ Subgroup.normalizer (F4 j4Facts.mat chkF_true : Set J) := by
  have hn := normal_F4 j4Facts.mat chkF_true
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h := hn.conj_mem ⟨x, F4_le_M4 j4Facts.mat chkF_true hx⟩
      (by rw [Subgroup.mem_subgroupOf]; exact hx) ⟨m, hm⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  · intro hx
    have h := hn.conj_mem ⟨m * x * m⁻¹, F4_le_M4 j4Facts.mat chkF_true hx⟩
      (by rw [Subgroup.mem_subgroupOf]; exact hx) ⟨m⁻¹, CFSG.Quasithin.KGJ4.M4.inv_mem hm⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa [mul_assoc] using h

theorem exists_orderOf_three_M4 :
    ∃ x ∈ CFSG.Quasithin.KGJ4.M4, orderOf x = 3 ∧
      4 ≤ Nat.card ↥(F4 j4Facts.mat chkF_true ⊓ Subgroup.centralizer ({x} : Set J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P', hP'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥CFSG.Quasithin.KGJ4.M4) 3
    (show 3 ^ 2 ∣ Nat.card ↥CFSG.Quasithin.KGJ4.M4 by
      rw [CFSG.Quasithin.J4M4Card.card_M4]; norm_num)
  have hPc : Nat.card ↥(P'.map CFSG.Quasithin.KGJ4.M4.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective CFSG.Quasithin.KGJ4.M4.subtype_injective, hP']
  have hPM : P'.map CFSG.Quasithin.KGJ4.M4.subtype ≤ CFSG.Quasithin.KGJ4.M4 :=
    Subgroup.map_subtype_le P'
  obtain ⟨x, hxP, hx3, h4⟩ := exists_orderOf_three_four_le_card (IsPGroup.of_card hPc)
    (hPM.trans M4_le_normalizer_F4) (c := 1) (by norm_num [card_F4 j4Facts.mat chkF_true])
    (by norm_num) (by rw [hPc, card_F4 j4Facts.mat chkF_true]; norm_num)
  exact ⟨x, hPM hxP, hx3, h4⟩

end CFSG.Quasithin.H13.Ch4.J4Blk
