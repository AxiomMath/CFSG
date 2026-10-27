module

public import CFSG.Quasithin.Recognition.M12AscEF
public import CFSG.Quasithin.Recognition.M12AscV
public import CFSG.Quasithin.Recognition.M12AscP2G
public import CFSG.Quasithin.Recognition.M12AscConj

public section

namespace CFSG.Quasithin

open Subgroup

variable {G : Type*} [Group G]

open CFSG.GH74.M12 (Asc03Hyp)

theorem mirror_claim [Finite G] [IsSimpleGroup G] {w : G} (hw : Asc03Hyp G w) (mw : AscModel w)
    {s : G} (hs : Asc03Hyp G s) (ms : AscModel s)
    (hsF : s ∈ mw.fSub) (hs1 : s ≠ 1) (hsw : s ≠ w) (hwQs : w ∈ ascQ s)
    {x' u' : G} (hx'H : x' ∈ ascH w) (hx'3 : x' * x' * x' = 1) (hx'1 : x' ≠ 1)
    (hu'2 : u' * u' = 1) (hu'Qs : u' ∈ ascQ s) (hu'x : u' * x' * u' = x'⁻¹)
    (hN : nrmG x' s = 1) : False := by
  classical
  have hw2 : w * w = 1 := asc_z_sq hw
  have hs2 : s * s = 1 := asc_z_sq hs
  have hsQw : s ∈ ascQ w := mw.fSub_le_ascQ hw hsF
  have hsH : s ∈ ascH w := ascQ_le_ascH w hsQw
  have hwF : w ∈ mw.fSub := mw.z_mem_fSub
  obtain ⟨-, hws⟩ := mw.fSub_elab hwF hsF
  have hu's : u' * s = s * u' :=
    Subgroup.mem_centralizer_singleton_iff.1 (ascQ_le_ascH s hu'Qs)
  have hxi : x'⁻¹ = x' * x' := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hx'3)
  have hx4 : x' * x' * (x' * x') = x' := by
    calc x' * x' * (x' * x') = (x' * x' * x') * x' := by group
      _ = x' := by rw [hx'3, one_mul]
  have hxx : x'⁻¹ * x'⁻¹ = x' := by rw [hxi]; exact hx4
  have hui : u'⁻¹ = u' := inv_eq_of_mul_eq_one_right hu'2
  set f : G := x' * s * x'⁻¹ with hf
  have hf' : f = x' * (s * (x' * x')) := by rw [hf, hxi]; group
  have hfF : f ∈ mw.fSub := mw.fSub_normal hx'H hsF
  have hN' : s * x' * s * x' * s * x' = 1 := by
    have : nrmG x' s = s * x' * s * (x' * x' * (x' * x')) * s * x' := by unfold nrmG; group
    rw [this, hx4] at hN
    exact hN
  have hu'x' : u' * x'⁻¹ * u' = x' := by
    calc u' * x'⁻¹ * u' = (u' * x' * u')⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, hui]; group
      _ = x' := by rw [hu'x, inv_inv]
  have hu'su' : u' * s * u' = s := by
    calc u' * s * u' = s * u' * u' := by rw [hu's]
      _ = s := by rw [mul_assoc, hu'2, mul_one]
  have huf : u' * f * u' = x'⁻¹ * s * x' := by
    calc u' * f * u' = u' * x' * (u' * u') * s * (u' * u') * x'⁻¹ * u' := by
          rw [hu'2, hf]; group
      _ = (u' * x' * u') * (u' * s * u') * (u' * x'⁻¹ * u') := by group
      _ = x'⁻¹ * s * x' := by rw [hu'x, hu'su', hu'x']
  set w' : G := f * u' with hw'
  have hw'sq : w' * w' = s := by
    calc w' * w' = f * (u' * f * u') := by rw [hw']; group
      _ = x' * s * (x'⁻¹ * x'⁻¹) * s * x' := by rw [huf, hf]; group
      _ = x' * s * x' * s * x' := by rw [hxx]
      _ = s := by
        have h1 : s * (x' * s * x' * s * x') = 1 := by
          calc s * (x' * s * x' * s * x') = s * x' * s * x' * s * x' := by group
            _ = 1 := hN'
        have h2 : x' * s * x' * s * x' = s⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [h2]
        exact inv_eq_of_mul_eq_one_right hs2
  have hw'H : w' ∈ ascH s := by
    rw [ascH, Subgroup.mem_centralizer_singleton_iff]
    calc w' * s = w' * (w' * w') := by rw [hw'sq]
      _ = (w' * w') * w' := by group
      _ = s * w' := by rw [hw'sq]
  have hw'Q : w' ∈ ascQ s := by
    have htb : tmul (ms.tb w') (ms.tb w') = zTab := by
      rw [← ms.tb_mul hw'H hw'H, hw'sq, ms.tb_z]
    exact (ms.mem_ascQ_iff_tb hs).2 ⟨hw'H, sq_eq_z_mem_q _ (ms.tb_mem hw'H) htb⟩
  have hfw : f = w' * u' := by
    rw [hw', mul_assoc, hu'2, mul_one]
  have hfQ : f ∈ ascQ s := by rw [hfw]; exact mul_mem hw'Q hu'Qs
  have hsQs : s ∈ ascQ s := AscModel.z_mem_ascQ hs
  have htbf : mw.tb f = tmul (mw.tb x') (tmul (mw.tb s) (tmul (mw.tb x') (mw.tb x'))) := by
    rw [hf', mw.tb_mul hx'H (mul_mem hsH (mul_mem hx'H hx'H)), mw.tb_mul hsH (mul_mem hx'H hx'H),
      mw.tb_mul hx'H hx'H]
  have hx'cube : tmul (mw.tb x') (tmul (mw.tb x') (mw.tb x')) = tid := by
    have h : x' * (x' * x') = 1 := by rw [← mul_assoc]; exact hx'3
    have := congrArg mw.tb h
    rwa [mw.tb_mul hx'H (mul_mem hx'H hx'H), mw.tb_mul hx'H hx'H, mw.tb_one] at this
  have hx'tid : mw.tb x' ≠ tid := fun h => hx'1 ((mw.eq_one_iff hx'H).2 h)
  have hsFt : mw.tb s ∈ FTabs := (mw.mem_fSub_iff.1 hsF).2
  have hs_tid : mw.tb s ≠ tid := fun h => hs1 ((mw.eq_one_iff hsH).2 h)
  have hs_z : mw.tb s ≠ zTab := fun h => hsw ((mw.eq_z_iff hsH).2 h)
  have hnrm : nrm (mw.tb x') (mw.tb s) = tid := by
    rw [← mw.tb_nrmG hx'H hsH, hN, mw.tb_one]
  obtain ⟨hf1, hf2, hf3, hf4⟩ := conj_not_in_span _ (mw.tb_mem hx'H) hx'cube hx'tid _ hsFt hs_tid
    hs_z hnrm
  rw [← htbf] at hf1 hf2 hf3 hf4
  have hf_ne1 : f ≠ 1 := fun h => hf1 (by rw [h, mw.tb_one])
  have hf_nez : f ≠ w := fun h => hf2 (by rw [h, mw.tb_z])
  have hf_nes : f ≠ s := fun h => hf3 (by rw [h])
  have hf_nezs : f ≠ w * s := fun h =>
    hf4 (by rw [h, mw.tb_mul (z_mem_ascH w) hsH, mw.tb_z])
  have hV4card : Nat.card (fourGroup w s hw2 hs2 hws) = 4 :=
    card_fourGroup (asc_z_ne_one hw) hs1 hsw
  have hV4Q : fourGroup w s hw2 hs2 hws ≤ ascQ s := by
    intro x hx
    rcases mem_fourGroup.1 hx with h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact hwQs
    · exact hsQs
    · exact mul_mem hwQs hsQs
  have hV4F : fourGroup w s hw2 hs2 hws ≤ mw.fSub := by
    intro x hx
    rcases mem_fourGroup.1 hx with h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact hwF
    · exact hsF
    · exact mul_mem hwF hsF
  have hfV4 : f ∉ fourGroup w s hw2 hs2 hws := by
    intro h
    rcases mem_fourGroup.1 h with h | h | h | h
    exacts [hf_ne1 h, hf_nez h, hf_nes h, hf_nezs h]
  have hBQ : fourGroup w s hw2 hs2 hws ⊔ zpowers f ≤ ascQ s :=
    sup_le hV4Q ((Subgroup.zpowers_le).2 hfQ)
  have hBF : fourGroup w s hw2 hs2 hws ⊔ zpowers f ≤ mw.fSub :=
    sup_le hV4F ((Subgroup.zpowers_le).2 hfF)
  have hVB : fourGroup w s hw2 hs2 hws ≤ fourGroup w s hw2 hs2 hws ⊔ zpowers f := le_sup_left
  have hfB : f ∈ fourGroup w s hw2 hs2 hws ⊔ zpowers f :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  have hBdvd : Nat.card ↥(fourGroup w s hw2 hs2 hws ⊔ zpowers f) ∣ 8 := by
    have := Subgroup.card_dvd_of_le hBF
    rwa [mw.card_fSub] at this
  have hVdvd : 4 ∣ Nat.card ↥(fourGroup w s hw2 hs2 hws ⊔ zpowers f) := by
    have := Subgroup.card_dvd_of_le hVB
    rwa [hV4card] at this
  have hB8 : Nat.card ↥(fourGroup w s hw2 hs2 hws ⊔ zpowers f) = 8 := by
    have hle := Nat.le_of_dvd (by norm_num) hBdvd
    have hpos : 0 < Nat.card ↥(fourGroup w s hw2 hs2 hws ⊔ zpowers f) := Nat.card_pos
    have hne : Nat.card ↥(fourGroup w s hw2 hs2 hws ⊔ zpowers f) ≠ 4 := by
      intro h4
      have : fourGroup w s hw2 hs2 hws = fourGroup w s hw2 hs2 hws ⊔ zpowers f :=
        Subgroup.eq_of_le_of_card_ge hVB (by rw [h4, hV4card])
      exact hfV4 (this ▸ hfB)
    obtain ⟨k, hk⟩ := hVdvd
    omega
  have hBeq : fourGroup w s hw2 hs2 hws ⊔ zpowers f = mw.fSub :=
    Subgroup.eq_of_le_of_card_ge hBF (by rw [hB8, mw.card_fSub])
  have hFQs : mw.fSub ≤ ascQ s := hBeq ▸ hBQ
  obtain ⟨g, hg⟩ := (mw.conj_mem_Q_iff hw hsQw hs1).2 hsF
  have hgz : g * w * g⁻¹ ≠ w := by rw [hg]; exact hsw
  have hsQ' : g * w * g⁻¹ ∈ ascQ w := by rw [hg]; exact hsQw
  obtain ⟨-, hE8, -, -⟩ := config_of_conj hw hgz hsQ'
  have hEF := mw.E_ne_fSub hw hgz hsQ'
  have hFE : mw.fSub ≤ ascQ w ⊓ (ascQ w).map (MulAut.conj g).toMonoidHom := by
    intro y hy
    refine ⟨mw.fSub_le_ascQ hw hy, ?_⟩
    rw [← ascQ_conj_eq w g, hg]
    exact hFQs hy
  exact hEF (Subgroup.eq_of_le_of_card_ge hFE (by rw [hE8, mw.card_fSub])).symm

end CFSG.Quasithin
