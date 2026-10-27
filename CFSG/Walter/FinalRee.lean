module

public import CFSG.Walter.W67.Section4.Prop41
public import CFSG.Walter.W67.Section5.Prop56
public import CFSG.Walter.W67.Section6.Lemma62
public import CFSG.Walter.Ree.Thompson3

public section

namespace CFSG.Walter

theorem walter_order_form_of_ree
    (h66 : W67.S_prop_6_6) (hR : W67.ReeIdentNative) :
    WalterOrderForm :=
  walter_order_form_of_W67 (W67.theorem_of_reeIdentNative h66 hR)

theorem walter_order_form_of_base
    (h62 : W67.S_lemma_6_2) (h65 : W67.S_lemma_6_5)
    (hbase : Ree.T2.BaseExists) :
    WalterOrderForm :=
  walter_order_form_of_ree (W67.prop_6_6_of W67.prop_4_1 W67.prop_5_6 h62 h65)
    (Ree.reeIdentNative hbase)

theorem walter_order_form_of_lemma65_base
    (h65 : W67.S_lemma_6_5) (hbase : Ree.T2.BaseExists) :
    WalterOrderForm :=
  walter_order_form_of_base (W67.lemma_6_2_of W67.prop_4_1 W67.prop_5_6) h65 hbase

end CFSG.Walter
