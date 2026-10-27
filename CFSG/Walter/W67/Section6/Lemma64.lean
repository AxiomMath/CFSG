module

public import CFSG.Walter.W67.Section6.Core64E
public import CFSG.Walter.W67.Section5.Prop56
public import CFSG.Walter.W67.Section6.Core64C

public section

namespace CFSG.Walter.W67

open Sec6

theorem lemma_6_4_of
    (h56 : S_prop_5_6) (h57 : S_lemma_5_7) : S_lemma_6_4 := by
  intro G _ _ s hR X hXE hX hsol
  obtain ⟨hXeq, ⟨σ⟩⟩ := nonempty_sol s h56 h57 hR hXE hX hsol
  subst hXeq
  exact ⟨rfl, σ.E7, σ.no_real_global, σ.sylow_three⟩

theorem lemma_6_4 :
    S_lemma_6_4 :=
  lemma_6_4_of prop_5_6 (lemma_5_7_of lemma_2_6_i IsJRSubgroup.nonempty_jrGroup prop_5_6)

end CFSG.Walter.W67
